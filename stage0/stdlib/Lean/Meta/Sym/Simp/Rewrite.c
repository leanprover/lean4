// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Rewrite
// Imports: public import Lean.Meta.Sym.Simp.Simproc public import Lean.Meta.Sym.Simp.Theorems public import Lean.Meta.Sym.Simp.App public import Lean.Meta.Sym.Simp.Discharger import Lean.Meta.ACLt import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InstantiateMVarsS import Init.Data.Range.Polymorphic.Iterators
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
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_match_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_acLt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(lean_object* v_expr_1_, lean_object* v_pattern_2_, lean_object* v_us_3_, lean_object* v_args_4_){
_start:
{
if (lean_obj_tag(v_expr_1_) == 4)
{
lean_object* v_us_9_; 
v_us_9_ = lean_ctor_get(v_expr_1_, 1);
if (lean_obj_tag(v_us_9_) == 0)
{
lean_object* v_declName_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
lean_dec_ref(v_pattern_2_);
v_declName_10_ = lean_ctor_get(v_expr_1_, 0);
lean_inc(v_declName_10_);
lean_dec_ref(v_expr_1_);
v___x_11_ = l_Lean_mkConst(v_declName_10_, v_us_3_);
v___x_12_ = l_Lean_mkAppN(v___x_11_, v_args_4_);
return v___x_12_;
}
else
{
goto v___jp_5_;
}
}
else
{
goto v___jp_5_;
}
v___jp_5_:
{
lean_object* v_levelParams_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_levelParams_6_ = lean_ctor_get(v_pattern_2_, 0);
lean_inc(v_levelParams_6_);
lean_dec_ref(v_pattern_2_);
v___x_7_ = l_Lean_Expr_instantiateLevelParams(v_expr_1_, v_levelParams_6_, v_us_3_);
lean_dec_ref(v_expr_1_);
v___x_8_ = l_Lean_mkAppN(v___x_7_, v_args_4_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue___boxed(lean_object* v_expr_13_, lean_object* v_pattern_14_, lean_object* v_us_15_, lean_object* v_args_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(v_expr_13_, v_pattern_14_, v_us_15_, v_args_16_);
lean_dec_ref(v_args_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(uint8_t v_perm_18_, lean_object* v_e_19_, lean_object* v_result_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
if (v_perm_18_ == 0)
{
uint8_t v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec_ref(v_result_20_);
lean_dec_ref(v_e_19_);
v___x_26_ = 1;
v___x_27_ = lean_box(v___x_26_);
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
else
{
uint8_t v___x_29_; lean_object* v___x_30_; 
v___x_29_ = 2;
v___x_30_ = l_Lean_Meta_acLt(v_result_20_, v_e_19_, v___x_29_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm___boxed(lean_object* v_perm_31_, lean_object* v_e_32_, lean_object* v_result_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_){
_start:
{
uint8_t v_perm_boxed_39_; lean_object* v_res_40_; 
v_perm_boxed_39_ = lean_unbox(v_perm_31_);
v_res_40_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_boxed_39_, v_e_32_, v_result_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(lean_object* v_l_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___x_44_; lean_object* v_mctx_45_; lean_object* v___x_46_; lean_object* v_fst_47_; lean_object* v_snd_48_; lean_object* v___x_49_; lean_object* v_cache_50_; lean_object* v_zetaDeltaFVarIds_51_; lean_object* v_postponed_52_; lean_object* v_diag_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_62_; 
v___x_44_ = lean_st_ref_get(v___y_42_);
v_mctx_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc_ref(v_mctx_45_);
lean_dec(v___x_44_);
v___x_46_ = lean_instantiate_level_mvars(v_mctx_45_, v_l_41_);
v_fst_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_fst_47_);
v_snd_48_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_snd_48_);
lean_dec_ref(v___x_46_);
v___x_49_ = lean_st_ref_take(v___y_42_);
v_cache_50_ = lean_ctor_get(v___x_49_, 1);
v_zetaDeltaFVarIds_51_ = lean_ctor_get(v___x_49_, 2);
v_postponed_52_ = lean_ctor_get(v___x_49_, 3);
v_diag_53_ = lean_ctor_get(v___x_49_, 4);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_49_);
if (v_isSharedCheck_62_ == 0)
{
lean_object* v_unused_63_; 
v_unused_63_ = lean_ctor_get(v___x_49_, 0);
lean_dec(v_unused_63_);
v___x_55_ = v___x_49_;
v_isShared_56_ = v_isSharedCheck_62_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_diag_53_);
lean_inc(v_postponed_52_);
lean_inc(v_zetaDeltaFVarIds_51_);
lean_inc(v_cache_50_);
lean_dec(v___x_49_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_62_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 0, v_fst_47_);
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_fst_47_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_cache_50_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v_zetaDeltaFVarIds_51_);
lean_ctor_set(v_reuseFailAlloc_61_, 3, v_postponed_52_);
lean_ctor_set(v_reuseFailAlloc_61_, 4, v_diag_53_);
v___x_58_ = v_reuseFailAlloc_61_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_st_ref_set(v___y_42_, v___x_58_);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v_snd_48_);
return v___x_60_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg___boxed(lean_object* v_l_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_l_64_, v___y_65_);
lean_dec(v___y_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(lean_object* v_l_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_l_68_, v___y_75_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___boxed(lean_object* v_l_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(v_l_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(lean_object* v_k_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___x_103_; 
lean_inc(v___y_97_);
lean_inc_ref(v___y_96_);
lean_inc(v___y_95_);
lean_inc_ref(v___y_94_);
lean_inc(v___y_93_);
v___x_103_ = lean_apply_10(v_k_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, lean_box(0));
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed(lean_object* v_k_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_k_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
lean_dec(v___y_105_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(lean_object* v_k_116_, uint8_t v_allowLevelAssignments_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v___f_128_; lean_object* v___x_129_; 
lean_inc(v___y_122_);
lean_inc_ref(v___y_121_);
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
lean_inc(v___y_118_);
v___f_128_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_128_, 0, v_k_116_);
lean_closure_set(v___f_128_, 1, v___y_118_);
lean_closure_set(v___f_128_, 2, v___y_119_);
lean_closure_set(v___f_128_, 3, v___y_120_);
lean_closure_set(v___f_128_, 4, v___y_121_);
lean_closure_set(v___f_128_, 5, v___y_122_);
v___x_129_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_117_, v___f_128_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
if (lean_obj_tag(v___x_129_) == 0)
{
return v___x_129_;
}
else
{
lean_object* v_a_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_137_; 
v_a_130_ = lean_ctor_get(v___x_129_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_129_);
if (v_isSharedCheck_137_ == 0)
{
v___x_132_ = v___x_129_;
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_a_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_137_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_135_; 
if (v_isShared_133_ == 0)
{
v___x_135_ = v___x_132_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_a_130_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___boxed(lean_object* v_k_138_, lean_object* v_allowLevelAssignments_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_150_; lean_object* v_res_151_; 
v_allowLevelAssignments_boxed_150_ = lean_unbox(v_allowLevelAssignments_139_);
v_res_151_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_k_138_, v_allowLevelAssignments_boxed_150_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(lean_object* v_00_u03b1_152_, lean_object* v_k_153_, uint8_t v_allowLevelAssignments_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_k_153_, v_allowLevelAssignments_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___boxed(lean_object* v_00_u03b1_166_, lean_object* v_k_167_, lean_object* v_allowLevelAssignments_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_179_; lean_object* v_res_180_; 
v_allowLevelAssignments_boxed_179_ = lean_unbox(v_allowLevelAssignments_168_);
v_res_180_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(v_00_u03b1_166_, v_k_167_, v_allowLevelAssignments_boxed_179_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = l_List_reverse___redArg(v_x_182_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
else
{
lean_object* v_head_195_; lean_object* v_tail_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_206_; 
v_head_195_ = lean_ctor_get(v_x_181_, 0);
v_tail_196_ = lean_ctor_get(v_x_181_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_206_ == 0)
{
v___x_198_ = v_x_181_;
v_isShared_199_ = v_isSharedCheck_206_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_tail_196_);
lean_inc(v_head_195_);
lean_dec(v_x_181_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_206_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v_a_201_; lean_object* v___x_203_; 
v___x_200_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_head_195_, v___y_189_);
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref(v___x_200_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 1, v_x_182_);
lean_ctor_set(v___x_198_, 0, v_a_201_);
v___x_203_ = v___x_198_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_201_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v_x_182_);
v___x_203_ = v_reuseFailAlloc_205_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
v_x_181_ = v_tail_196_;
v_x_182_ = v___x_203_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1___boxed(lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_x_207_, v_x_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(lean_object* v_x_220_, lean_object* v_x_221_, lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_ks_224_; lean_object* v_vs_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_249_; 
v_ks_224_ = lean_ctor_get(v_x_220_, 0);
v_vs_225_ = lean_ctor_get(v_x_220_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_220_);
if (v_isSharedCheck_249_ == 0)
{
v___x_227_ = v_x_220_;
v_isShared_228_ = v_isSharedCheck_249_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_vs_225_);
lean_inc(v_ks_224_);
lean_dec(v_x_220_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_249_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_229_ = lean_array_get_size(v_ks_224_);
v___x_230_ = lean_nat_dec_lt(v_x_221_, v___x_229_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
lean_dec(v_x_221_);
v___x_231_ = lean_array_push(v_ks_224_, v_x_222_);
v___x_232_ = lean_array_push(v_vs_225_, v_x_223_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 1, v___x_232_);
lean_ctor_set(v___x_227_, 0, v___x_231_);
v___x_234_ = v___x_227_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
else
{
lean_object* v_k_x27_236_; uint8_t v___x_237_; 
v_k_x27_236_ = lean_array_fget_borrowed(v_ks_224_, v_x_221_);
v___x_237_ = l_Lean_instBEqMVarId_beq(v_x_222_, v_k_x27_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_239_; 
if (v_isShared_228_ == 0)
{
v___x_239_ = v___x_227_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_ks_224_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_vs_225_);
v___x_239_ = v_reuseFailAlloc_243_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_x_221_, v___x_240_);
lean_dec(v_x_221_);
v_x_220_ = v___x_239_;
v_x_221_ = v___x_241_;
goto _start;
}
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_244_ = lean_array_fset(v_ks_224_, v_x_221_, v_x_222_);
v___x_245_ = lean_array_fset(v_vs_225_, v_x_221_, v_x_223_);
lean_dec(v_x_221_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 1, v___x_245_);
lean_ctor_set(v___x_227_, 0, v___x_244_);
v___x_247_ = v___x_227_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_245_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_n_250_, lean_object* v_k_251_, lean_object* v_v_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(v_n_250_, v___x_253_, v_k_251_, v_v_252_);
return v___x_254_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0(void){
_start:
{
size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; 
v___x_255_ = ((size_t)5ULL);
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_shift_left(v___x_256_, v___x_255_);
return v___x_257_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_258_; size_t v___x_259_; size_t v___x_260_; 
v___x_258_ = ((size_t)1ULL);
v___x_259_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0);
v___x_260_ = lean_usize_sub(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(lean_object* v_x_262_, size_t v_x_263_, size_t v_x_264_, lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_object* v_es_267_; size_t v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; lean_object* v_j_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_es_267_ = lean_ctor_get(v_x_262_, 0);
v___x_268_ = ((size_t)5ULL);
v___x_269_ = ((size_t)1ULL);
v___x_270_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1);
v___x_271_ = lean_usize_land(v_x_263_, v___x_270_);
v_j_272_ = lean_usize_to_nat(v___x_271_);
v___x_273_ = lean_array_get_size(v_es_267_);
v___x_274_ = lean_nat_dec_lt(v_j_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_dec(v_j_272_);
lean_dec(v_x_266_);
lean_dec(v_x_265_);
return v_x_262_;
}
else
{
lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_311_; 
lean_inc_ref(v_es_267_);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; 
v_unused_312_ = lean_ctor_get(v_x_262_, 0);
lean_dec(v_unused_312_);
v___x_276_ = v_x_262_;
v_isShared_277_ = v_isSharedCheck_311_;
goto v_resetjp_275_;
}
else
{
lean_dec(v_x_262_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_311_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_v_278_; lean_object* v___x_279_; lean_object* v_xs_x27_280_; lean_object* v___y_282_; 
v_v_278_ = lean_array_fget(v_es_267_, v_j_272_);
v___x_279_ = lean_box(0);
v_xs_x27_280_ = lean_array_fset(v_es_267_, v_j_272_, v___x_279_);
switch(lean_obj_tag(v_v_278_))
{
case 0:
{
lean_object* v_key_287_; lean_object* v_val_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_298_; 
v_key_287_ = lean_ctor_get(v_v_278_, 0);
v_val_288_ = lean_ctor_get(v_v_278_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_v_278_);
if (v_isSharedCheck_298_ == 0)
{
v___x_290_ = v_v_278_;
v_isShared_291_ = v_isSharedCheck_298_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_val_288_);
lean_inc(v_key_287_);
lean_dec(v_v_278_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_298_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
uint8_t v___x_292_; 
v___x_292_ = l_Lean_instBEqMVarId_beq(v_x_265_, v_key_287_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_del_object(v___x_290_);
v___x_293_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_287_, v_val_288_, v_x_265_, v_x_266_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
v___y_282_ = v___x_294_;
goto v___jp_281_;
}
else
{
lean_object* v___x_296_; 
lean_dec(v_val_288_);
lean_dec(v_key_287_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 1, v_x_266_);
lean_ctor_set(v___x_290_, 0, v_x_265_);
v___x_296_ = v___x_290_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_x_265_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_x_266_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
v___y_282_ = v___x_296_;
goto v___jp_281_;
}
}
}
}
case 1:
{
lean_object* v_node_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_309_; 
v_node_299_ = lean_ctor_get(v_v_278_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v_v_278_);
if (v_isSharedCheck_309_ == 0)
{
v___x_301_ = v_v_278_;
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_node_299_);
lean_dec(v_v_278_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_309_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
size_t v___x_303_; size_t v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
v___x_303_ = lean_usize_shift_right(v_x_263_, v___x_268_);
v___x_304_ = lean_usize_add(v_x_264_, v___x_269_);
v___x_305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_node_299_, v___x_303_, v___x_304_, v_x_265_, v_x_266_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_305_);
v___x_307_ = v___x_301_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v___x_305_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
v___y_282_ = v___x_307_;
goto v___jp_281_;
}
}
}
default: 
{
lean_object* v___x_310_; 
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v_x_265_);
lean_ctor_set(v___x_310_, 1, v_x_266_);
v___y_282_ = v___x_310_;
goto v___jp_281_;
}
}
v___jp_281_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_array_fset(v_xs_x27_280_, v_j_272_, v___y_282_);
lean_dec(v_j_272_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 0, v___x_283_);
v___x_285_ = v___x_276_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
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
}
else
{
lean_object* v_ks_313_; lean_object* v_vs_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_334_; 
v_ks_313_ = lean_ctor_get(v_x_262_, 0);
v_vs_314_ = lean_ctor_get(v_x_262_, 1);
v_isSharedCheck_334_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_334_ == 0)
{
v___x_316_ = v_x_262_;
v_isShared_317_ = v_isSharedCheck_334_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_vs_314_);
lean_inc(v_ks_313_);
lean_dec(v_x_262_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_334_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_ks_313_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_vs_314_);
v___x_319_ = v_reuseFailAlloc_333_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v_newNode_320_; uint8_t v___y_322_; size_t v___x_328_; uint8_t v___x_329_; 
v_newNode_320_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(v___x_319_, v_x_265_, v_x_266_);
v___x_328_ = ((size_t)7ULL);
v___x_329_ = lean_usize_dec_le(v___x_328_, v_x_264_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_330_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_320_);
v___x_331_ = lean_unsigned_to_nat(4u);
v___x_332_ = lean_nat_dec_lt(v___x_330_, v___x_331_);
lean_dec(v___x_330_);
v___y_322_ = v___x_332_;
goto v___jp_321_;
}
else
{
v___y_322_ = v___x_329_;
goto v___jp_321_;
}
v___jp_321_:
{
if (v___y_322_ == 0)
{
lean_object* v_ks_323_; lean_object* v_vs_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_ks_323_ = lean_ctor_get(v_newNode_320_, 0);
lean_inc_ref(v_ks_323_);
v_vs_324_ = lean_ctor_get(v_newNode_320_, 1);
lean_inc_ref(v_vs_324_);
lean_dec_ref(v_newNode_320_);
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2);
v___x_327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_x_264_, v_ks_323_, v_vs_324_, v___x_325_, v___x_326_);
lean_dec_ref(v_vs_324_);
lean_dec_ref(v_ks_323_);
return v___x_327_;
}
else
{
return v_newNode_320_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(size_t v_depth_335_, lean_object* v_keys_336_, lean_object* v_vals_337_, lean_object* v_i_338_, lean_object* v_entries_339_){
_start:
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = lean_array_get_size(v_keys_336_);
v___x_341_ = lean_nat_dec_lt(v_i_338_, v___x_340_);
if (v___x_341_ == 0)
{
lean_dec(v_i_338_);
return v_entries_339_;
}
else
{
lean_object* v_k_342_; lean_object* v_v_343_; uint64_t v___x_344_; size_t v_h_345_; size_t v___x_346_; lean_object* v___x_347_; size_t v___x_348_; size_t v___x_349_; size_t v___x_350_; size_t v_h_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_k_342_ = lean_array_fget_borrowed(v_keys_336_, v_i_338_);
v_v_343_ = lean_array_fget_borrowed(v_vals_337_, v_i_338_);
v___x_344_ = l_Lean_instHashableMVarId_hash(v_k_342_);
v_h_345_ = lean_uint64_to_usize(v___x_344_);
v___x_346_ = ((size_t)5ULL);
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_sub(v_depth_335_, v___x_348_);
v___x_350_ = lean_usize_mul(v___x_346_, v___x_349_);
v_h_351_ = lean_usize_shift_right(v_h_345_, v___x_350_);
v___x_352_ = lean_nat_add(v_i_338_, v___x_347_);
lean_dec(v_i_338_);
lean_inc(v_v_343_);
lean_inc(v_k_342_);
v___x_353_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_entries_339_, v_h_351_, v_depth_335_, v_k_342_, v_v_343_);
v_i_338_ = v___x_352_;
v_entries_339_ = v___x_353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_depth_355_, lean_object* v_keys_356_, lean_object* v_vals_357_, lean_object* v_i_358_, lean_object* v_entries_359_){
_start:
{
size_t v_depth_boxed_360_; lean_object* v_res_361_; 
v_depth_boxed_360_ = lean_unbox_usize(v_depth_355_);
lean_dec(v_depth_355_);
v_res_361_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_depth_boxed_360_, v_keys_356_, v_vals_357_, v_i_358_, v_entries_359_);
lean_dec_ref(v_vals_357_);
lean_dec_ref(v_keys_356_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
size_t v_x_34062__boxed_367_; size_t v_x_34063__boxed_368_; lean_object* v_res_369_; 
v_x_34062__boxed_367_ = lean_unbox_usize(v_x_363_);
lean_dec(v_x_363_);
v_x_34063__boxed_368_ = lean_unbox_usize(v_x_364_);
lean_dec(v_x_364_);
v_res_369_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_362_, v_x_34062__boxed_367_, v_x_34063__boxed_368_, v_x_365_, v_x_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_x_372_){
_start:
{
uint64_t v___x_373_; size_t v___x_374_; size_t v___x_375_; lean_object* v___x_376_; 
v___x_373_ = l_Lean_instHashableMVarId_hash(v_x_371_);
v___x_374_ = lean_uint64_to_usize(v___x_373_);
v___x_375_ = ((size_t)1ULL);
v___x_376_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_370_, v___x_374_, v___x_375_, v_x_371_, v_x_372_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(lean_object* v_mvarId_377_, lean_object* v_val_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; lean_object* v_mctx_382_; lean_object* v_cache_383_; lean_object* v_zetaDeltaFVarIds_384_; lean_object* v_postponed_385_; lean_object* v_diag_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_413_; 
v___x_381_ = lean_st_ref_take(v___y_379_);
v_mctx_382_ = lean_ctor_get(v___x_381_, 0);
v_cache_383_ = lean_ctor_get(v___x_381_, 1);
v_zetaDeltaFVarIds_384_ = lean_ctor_get(v___x_381_, 2);
v_postponed_385_ = lean_ctor_get(v___x_381_, 3);
v_diag_386_ = lean_ctor_get(v___x_381_, 4);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_413_ == 0)
{
v___x_388_ = v___x_381_;
v_isShared_389_ = v_isSharedCheck_413_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_diag_386_);
lean_inc(v_postponed_385_);
lean_inc(v_zetaDeltaFVarIds_384_);
lean_inc(v_cache_383_);
lean_inc(v_mctx_382_);
lean_dec(v___x_381_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_413_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v_depth_390_; lean_object* v_levelAssignDepth_391_; lean_object* v_mvarCounter_392_; lean_object* v_lDepth_393_; lean_object* v_decls_394_; lean_object* v_userNames_395_; lean_object* v_lAssignment_396_; lean_object* v_eAssignment_397_; lean_object* v_dAssignment_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_412_; 
v_depth_390_ = lean_ctor_get(v_mctx_382_, 0);
v_levelAssignDepth_391_ = lean_ctor_get(v_mctx_382_, 1);
v_mvarCounter_392_ = lean_ctor_get(v_mctx_382_, 2);
v_lDepth_393_ = lean_ctor_get(v_mctx_382_, 3);
v_decls_394_ = lean_ctor_get(v_mctx_382_, 4);
v_userNames_395_ = lean_ctor_get(v_mctx_382_, 5);
v_lAssignment_396_ = lean_ctor_get(v_mctx_382_, 6);
v_eAssignment_397_ = lean_ctor_get(v_mctx_382_, 7);
v_dAssignment_398_ = lean_ctor_get(v_mctx_382_, 8);
v_isSharedCheck_412_ = !lean_is_exclusive(v_mctx_382_);
if (v_isSharedCheck_412_ == 0)
{
v___x_400_ = v_mctx_382_;
v_isShared_401_ = v_isSharedCheck_412_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_dAssignment_398_);
lean_inc(v_eAssignment_397_);
lean_inc(v_lAssignment_396_);
lean_inc(v_userNames_395_);
lean_inc(v_decls_394_);
lean_inc(v_lDepth_393_);
lean_inc(v_mvarCounter_392_);
lean_inc(v_levelAssignDepth_391_);
lean_inc(v_depth_390_);
lean_dec(v_mctx_382_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_412_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_eAssignment_397_, v_mvarId_377_, v_val_378_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 7, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_depth_390_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_levelAssignDepth_391_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_mvarCounter_392_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_lDepth_393_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_decls_394_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v_userNames_395_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_lAssignment_396_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v_dAssignment_398_);
v___x_404_ = v_reuseFailAlloc_411_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_404_);
v___x_406_ = v___x_388_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_cache_383_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_zetaDeltaFVarIds_384_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_postponed_385_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_diag_386_);
v___x_406_ = v_reuseFailAlloc_410_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_407_ = lean_st_ref_set(v___y_379_, v___x_406_);
v___x_408_ = lean_box(0);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(lean_object* v_mvarId_414_, lean_object* v_val_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_414_, v_val_415_, v___y_416_);
lean_dec(v___y_416_);
return v_res_418_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_keys_419_, lean_object* v_i_420_, lean_object* v_k_421_){
_start:
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = lean_array_get_size(v_keys_419_);
v___x_423_ = lean_nat_dec_lt(v_i_420_, v___x_422_);
if (v___x_423_ == 0)
{
lean_dec(v_i_420_);
return v___x_423_;
}
else
{
lean_object* v_k_x27_424_; uint8_t v___x_425_; 
v_k_x27_424_ = lean_array_fget_borrowed(v_keys_419_, v_i_420_);
v___x_425_ = l_Lean_instBEqMVarId_beq(v_k_421_, v_k_x27_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_unsigned_to_nat(1u);
v___x_427_ = lean_nat_add(v_i_420_, v___x_426_);
lean_dec(v_i_420_);
v_i_420_ = v___x_427_;
goto _start;
}
else
{
lean_dec(v_i_420_);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_keys_429_, lean_object* v_i_430_, lean_object* v_k_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_keys_429_, v_i_430_, v_k_431_);
lean_dec(v_k_431_);
lean_dec_ref(v_keys_429_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(lean_object* v_x_434_, size_t v_x_435_, lean_object* v_x_436_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v_es_437_; lean_object* v___x_438_; size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; lean_object* v_j_442_; lean_object* v___x_443_; 
v_es_437_ = lean_ctor_get(v_x_434_, 0);
v___x_438_ = lean_box(2);
v___x_439_ = ((size_t)5ULL);
v___x_440_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1);
v___x_441_ = lean_usize_land(v_x_435_, v___x_440_);
v_j_442_ = lean_usize_to_nat(v___x_441_);
v___x_443_ = lean_array_get_borrowed(v___x_438_, v_es_437_, v_j_442_);
lean_dec(v_j_442_);
switch(lean_obj_tag(v___x_443_))
{
case 0:
{
lean_object* v_key_444_; uint8_t v___x_445_; 
v_key_444_ = lean_ctor_get(v___x_443_, 0);
v___x_445_ = l_Lean_instBEqMVarId_beq(v_x_436_, v_key_444_);
return v___x_445_;
}
case 1:
{
lean_object* v_node_446_; size_t v___x_447_; 
v_node_446_ = lean_ctor_get(v___x_443_, 0);
v___x_447_ = lean_usize_shift_right(v_x_435_, v___x_439_);
v_x_434_ = v_node_446_;
v_x_435_ = v___x_447_;
goto _start;
}
default: 
{
uint8_t v___x_449_; 
v___x_449_ = 0;
return v___x_449_;
}
}
}
else
{
lean_object* v_ks_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_ks_450_ = lean_ctor_get(v_x_434_, 0);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_ks_450_, v___x_451_, v_x_436_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
size_t v_x_34300__boxed_456_; uint8_t v_res_457_; lean_object* v_r_458_; 
v_x_34300__boxed_456_ = lean_unbox_usize(v_x_454_);
lean_dec(v_x_454_);
v_res_457_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_453_, v_x_34300__boxed_456_, v_x_455_);
lean_dec(v_x_455_);
lean_dec_ref(v_x_453_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
uint64_t v___x_461_; size_t v___x_462_; uint8_t v___x_463_; 
v___x_461_ = l_Lean_instHashableMVarId_hash(v_x_460_);
v___x_462_ = lean_uint64_to_usize(v___x_461_);
v___x_463_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_459_, v___x_462_, v_x_460_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg___boxed(lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_464_, v_x_465_);
lean_dec(v_x_465_);
lean_dec_ref(v_x_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(lean_object* v_mvarId_468_, lean_object* v___y_469_){
_start:
{
lean_object* v___x_471_; lean_object* v_mctx_472_; lean_object* v_eAssignment_473_; uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_471_ = lean_st_ref_get(v___y_469_);
v_mctx_472_ = lean_ctor_get(v___x_471_, 0);
lean_inc_ref(v_mctx_472_);
lean_dec(v___x_471_);
v_eAssignment_473_ = lean_ctor_get(v_mctx_472_, 7);
lean_inc_ref(v_eAssignment_473_);
lean_dec_ref(v_mctx_472_);
v___x_474_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_eAssignment_473_, v_mvarId_468_);
lean_dec_ref(v_eAssignment_473_);
v___x_475_ = lean_box(v___x_474_);
v___x_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_476_, 0, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg___boxed(lean_object* v_mvarId_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec(v_mvarId_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(lean_object* v_upperBound_481_, lean_object* v_d_482_, lean_object* v_a_483_, lean_object* v_b_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_a_496_; uint8_t v___x_500_; 
v___x_500_ = lean_nat_dec_lt(v_a_483_, v_upperBound_481_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_dec(v_a_483_);
lean_dec_ref(v_d_482_);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v_b_484_);
return v___x_501_;
}
else
{
lean_object* v_snd_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_636_; 
v_snd_502_ = lean_ctor_get(v_b_484_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v_b_484_);
if (v_isSharedCheck_636_ == 0)
{
lean_object* v_unused_637_; 
v_unused_637_ = lean_ctor_get(v_b_484_, 0);
lean_dec(v_unused_637_);
v___x_504_ = v_b_484_;
v_isShared_505_ = v_isSharedCheck_636_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_snd_502_);
lean_dec(v_b_484_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_636_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_fst_506_; lean_object* v_snd_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_635_; 
v_fst_506_ = lean_ctor_get(v_snd_502_, 0);
v_snd_507_ = lean_ctor_get(v_snd_502_, 1);
v_isSharedCheck_635_ = !lean_is_exclusive(v_snd_502_);
if (v_isSharedCheck_635_ == 0)
{
v___x_509_ = v_snd_502_;
v_isShared_510_ = v_isSharedCheck_635_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snd_507_);
lean_inc(v_fst_506_);
lean_dec(v_snd_502_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_635_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_box(0);
v___x_512_ = lean_array_fget_borrowed(v_fst_506_, v_a_483_);
if (lean_obj_tag(v___x_512_) == 2)
{
lean_object* v_mvarId_513_; lean_object* v___x_514_; 
v_mvarId_513_ = lean_ctor_get(v___x_512_, 0);
v___x_514_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_513_, v___y_491_);
if (lean_obj_tag(v___x_514_) == 0)
{
lean_object* v_a_515_; uint8_t v___x_516_; 
v_a_515_ = lean_ctor_get(v___x_514_, 0);
lean_inc(v_a_515_);
lean_dec_ref(v___x_514_);
v___x_516_ = lean_unbox(v_a_515_);
lean_dec(v_a_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_inc(v_mvarId_513_);
v___x_517_ = l_Lean_MVarId_getDecl(v_mvarId_513_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_a_518_; lean_object* v_type_519_; lean_object* v___x_520_; 
v_a_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_a_518_);
lean_dec_ref(v___x_517_);
v_type_519_ = lean_ctor_get(v_a_518_, 2);
lean_inc_ref(v_type_519_);
lean_dec(v_a_518_);
lean_inc_ref(v_d_482_);
lean_inc(v___y_493_);
lean_inc_ref(v___y_492_);
lean_inc(v___y_491_);
lean_inc_ref(v___y_490_);
lean_inc(v___y_489_);
lean_inc_ref(v___y_488_);
lean_inc(v___y_487_);
lean_inc_ref(v___y_486_);
lean_inc(v___y_485_);
v___x_520_ = lean_apply_11(v_d_482_, v_type_519_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, lean_box(0));
if (lean_obj_tag(v___x_520_) == 0)
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_569_; 
v_a_521_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_569_ == 0)
{
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_569_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_520_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_569_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
uint8_t v___y_526_; 
if (lean_obj_tag(v_a_521_) == 0)
{
uint8_t v___x_539_; 
lean_dec(v_a_483_);
lean_dec_ref(v_d_482_);
v___x_539_ = lean_unbox(v_snd_507_);
lean_dec(v_snd_507_);
if (v___x_539_ == 0)
{
uint8_t v_contextDependent_540_; 
v_contextDependent_540_ = lean_ctor_get_uint8(v_a_521_, 0);
lean_dec_ref(v_a_521_);
v___y_526_ = v_contextDependent_540_;
goto v___jp_525_;
}
else
{
lean_dec_ref(v_a_521_);
v___y_526_ = v___x_500_;
goto v___jp_525_;
}
}
else
{
lean_object* v_proof_541_; uint8_t v_contextDependent_542_; uint8_t v___y_544_; uint8_t v___x_568_; 
lean_del_object(v___x_523_);
lean_del_object(v___x_509_);
lean_del_object(v___x_504_);
v_proof_541_ = lean_ctor_get(v_a_521_, 0);
lean_inc_ref(v_proof_541_);
v_contextDependent_542_ = lean_ctor_get_uint8(v_a_521_, sizeof(void*)*1);
lean_dec_ref(v_a_521_);
v___x_568_ = lean_unbox(v_snd_507_);
lean_dec(v_snd_507_);
if (v___x_568_ == 0)
{
v___y_544_ = v_contextDependent_542_;
goto v___jp_543_;
}
else
{
v___y_544_ = v___x_500_;
goto v___jp_543_;
}
v___jp_543_:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Meta_Sym_instantiateMVarsS(v_proof_541_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc_n(v_a_546_, 2);
lean_dec_ref(v___x_545_);
lean_inc(v_mvarId_513_);
v___x_547_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_513_, v_a_546_, v___y_491_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec_ref(v___x_547_);
v___x_548_ = lean_array_fset(v_fst_506_, v_a_483_, v_a_546_);
v___x_549_ = lean_box(v___y_544_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_548_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_511_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v_a_496_ = v___x_551_;
goto v___jp_495_;
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec(v_a_546_);
lean_dec(v_fst_506_);
lean_dec(v_a_483_);
lean_dec_ref(v_d_482_);
v_a_552_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_547_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_547_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_fst_506_);
lean_dec(v_a_483_);
lean_dec_ref(v_d_482_);
v_a_560_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v___x_545_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_545_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
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
v___jp_525_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_527_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_526_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
v___x_529_ = lean_box(v___y_526_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v___x_529_);
v___x_531_ = v___x_509_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_fst_506_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_529_);
v___x_531_ = v_reuseFailAlloc_538_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_533_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_531_);
lean_ctor_set(v___x_504_, 0, v___x_528_);
v___x_533_ = v___x_504_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_531_);
v___x_533_ = v_reuseFailAlloc_537_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
lean_object* v___x_535_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_533_);
v___x_535_ = v___x_523_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_del_object(v___x_509_);
lean_dec(v_snd_507_);
lean_dec(v_fst_506_);
lean_del_object(v___x_504_);
lean_dec(v_a_483_);
lean_dec_ref(v_d_482_);
v_a_570_ = lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_520_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_520_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_520_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_del_object(v___x_509_);
lean_dec(v_snd_507_);
lean_dec(v_fst_506_);
lean_del_object(v___x_504_);
lean_dec(v_a_483_);
lean_dec_ref(v_d_482_);
v_a_578_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_517_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_517_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v___x_586_; 
lean_inc_ref(v___x_512_);
v___x_586_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_512_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref(v___x_586_);
v___x_588_ = lean_array_fset(v_fst_506_, v_a_483_, v_a_587_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_588_);
v___x_590_ = v___x_509_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_snd_507_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_590_);
lean_ctor_set(v___x_504_, 0, v___x_511_);
v___x_592_ = v___x_504_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
v_a_496_ = v___x_592_;
goto v___jp_495_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_del_object(v___x_509_);
lean_dec(v_snd_507_);
lean_dec(v_fst_506_);
lean_del_object(v___x_504_);
lean_dec(v_a_483_);
lean_dec_ref(v_d_482_);
v_a_595_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_586_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_586_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_del_object(v___x_509_);
lean_dec(v_snd_507_);
lean_dec(v_fst_506_);
lean_del_object(v___x_504_);
lean_dec(v_a_483_);
lean_dec_ref(v_d_482_);
v_a_603_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_514_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_514_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
uint8_t v___x_611_; 
v___x_611_ = l_Lean_Expr_hasMVar(v___x_512_);
if (v___x_611_ == 0)
{
lean_object* v___x_613_; 
if (v_isShared_510_ == 0)
{
v___x_613_ = v___x_509_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_fst_506_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_snd_507_);
v___x_613_ = v_reuseFailAlloc_617_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_613_);
lean_ctor_set(v___x_504_, 0, v___x_511_);
v___x_615_ = v___x_504_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
v_a_496_ = v___x_615_;
goto v___jp_495_;
}
}
}
else
{
lean_object* v___x_618_; 
lean_inc(v___x_512_);
v___x_618_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_512_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref(v___x_618_);
v___x_620_ = lean_array_fset(v_fst_506_, v_a_483_, v_a_619_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_620_);
v___x_622_ = v___x_509_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_snd_507_);
v___x_622_ = v_reuseFailAlloc_626_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_622_);
lean_ctor_set(v___x_504_, 0, v___x_511_);
v___x_624_ = v___x_504_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
v_a_496_ = v___x_624_;
goto v___jp_495_;
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_del_object(v___x_509_);
lean_dec(v_snd_507_);
lean_dec(v_fst_506_);
lean_del_object(v___x_504_);
lean_dec(v_a_483_);
lean_dec_ref(v_d_482_);
v_a_627_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_618_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_618_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
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
}
}
}
v___jp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = lean_nat_add(v_a_483_, v___x_497_);
lean_dec(v_a_483_);
v_a_483_ = v___x_498_;
v_b_484_ = v_a_496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg___boxed(lean_object* v_upperBound_638_, lean_object* v_d_639_, lean_object* v_a_640_, lean_object* v_b_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_upperBound_638_, v_d_639_, v_a_640_, v_b_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec(v_upperBound_638_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object* v_pattern_655_, lean_object* v_e_656_, uint8_t v___x_657_, lean_object* v_d_658_, lean_object* v_expr_659_, lean_object* v_rhs_660_, uint8_t v_perm_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; 
lean_inc_ref(v_e_656_);
lean_inc_ref(v_pattern_655_);
v___x_672_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_655_, v_e_656_, v___x_657_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_789_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_789_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_789_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_789_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
if (lean_obj_tag(v_a_673_) == 1)
{
lean_object* v_val_677_; lean_object* v_us_678_; lean_object* v_args_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_784_; 
lean_del_object(v___x_675_);
v_val_677_ = lean_ctor_get(v_a_673_, 0);
lean_inc(v_val_677_);
lean_dec_ref(v_a_673_);
v_us_678_ = lean_ctor_get(v_val_677_, 0);
v_args_679_ = lean_ctor_get(v_val_677_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_val_677_);
if (v_isSharedCheck_784_ == 0)
{
v___x_681_ = v_val_677_;
v_isShared_682_ = v_isSharedCheck_784_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_args_679_);
lean_inc(v_us_678_);
lean_dec(v_val_677_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_784_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = lean_box(0);
v___x_684_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_us_678_, v___x_683_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_692_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref(v___x_684_);
v___x_686_ = lean_array_get_size(v_args_679_);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = 0;
v___x_689_ = lean_box(0);
v___x_690_ = lean_box(v___x_688_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_690_);
lean_ctor_set(v___x_681_, 0, v_args_679_);
v___x_692_ = v___x_681_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_args_679_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_690_);
v___x_692_ = v_reuseFailAlloc_775_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_689_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v___x_686_, v_d_658_, v___x_687_, v___x_693_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_766_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_766_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_766_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_766_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_fst_699_; 
v_fst_699_ = lean_ctor_get(v_a_695_, 0);
if (lean_obj_tag(v_fst_699_) == 0)
{
lean_object* v_snd_700_; lean_object* v_fst_701_; lean_object* v_snd_702_; lean_object* v_levelParams_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
lean_del_object(v___x_697_);
v_snd_700_ = lean_ctor_get(v_a_695_, 1);
lean_inc(v_snd_700_);
lean_dec(v_a_695_);
v_fst_701_ = lean_ctor_get(v_snd_700_, 0);
lean_inc(v_fst_701_);
v_snd_702_ = lean_ctor_get(v_snd_700_, 1);
lean_inc(v_snd_702_);
lean_dec(v_snd_700_);
v_levelParams_703_ = lean_ctor_get(v_pattern_655_, 0);
lean_inc(v_levelParams_703_);
lean_inc(v_a_685_);
v___x_704_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(v_expr_659_, v_pattern_655_, v_a_685_, v_fst_701_);
v___x_705_ = l_Lean_Expr_instantiateLevelParams(v_rhs_660_, v_levelParams_703_, v_a_685_);
v___x_706_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_705_, v___y_666_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v___x_706_);
v___x_708_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_a_707_, v_fst_701_, v___y_666_);
lean_dec(v_fst_701_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_745_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_745_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_745_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_745_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
uint8_t v___x_713_; 
v___x_713_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_656_, v_a_709_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
lean_inc(v_a_709_);
v___x_714_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_661_, v_e_656_, v_a_709_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_731_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_731_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_731_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_731_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
uint8_t v___x_725_; 
v___x_725_ = lean_unbox(v_a_715_);
lean_dec(v_a_715_);
if (v___x_725_ == 0)
{
lean_del_object(v___x_711_);
lean_dec(v_a_709_);
lean_dec_ref(v___x_704_);
goto v___jp_719_;
}
else
{
if (v___x_713_ == 0)
{
lean_object* v___x_726_; uint8_t v___x_727_; lean_object* v___x_729_; 
lean_del_object(v___x_717_);
v___x_726_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_726_, 0, v_a_709_);
lean_ctor_set(v___x_726_, 1, v___x_704_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*2, v___x_688_);
v___x_727_ = lean_unbox(v_snd_702_);
lean_dec(v_snd_702_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*2 + 1, v___x_727_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_726_);
v___x_729_ = v___x_711_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_726_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
else
{
lean_del_object(v___x_711_);
lean_dec(v_a_709_);
lean_dec_ref(v___x_704_);
goto v___jp_719_;
}
}
v___jp_719_:
{
uint8_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
v___x_720_ = lean_unbox(v_snd_702_);
lean_dec(v_snd_702_);
v___x_721_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_720_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v___x_721_);
v___x_723_ = v___x_717_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_del_object(v___x_711_);
lean_dec(v_a_709_);
lean_dec_ref(v___x_704_);
lean_dec(v_snd_702_);
v_a_732_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_714_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_714_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
else
{
uint8_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
lean_dec(v_a_709_);
lean_dec_ref(v___x_704_);
lean_dec_ref(v_e_656_);
v___x_740_ = lean_unbox(v_snd_702_);
lean_dec(v_snd_702_);
v___x_741_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_740_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_741_);
v___x_743_ = v___x_711_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
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
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v___x_704_);
lean_dec(v_snd_702_);
lean_dec_ref(v_e_656_);
v_a_746_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_708_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_708_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v___x_704_);
lean_dec(v_snd_702_);
lean_dec(v_fst_701_);
lean_dec_ref(v_e_656_);
v_a_754_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_706_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_706_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_val_762_; lean_object* v___x_764_; 
lean_inc_ref(v_fst_699_);
lean_dec(v_a_695_);
lean_dec(v_a_685_);
lean_dec_ref(v_expr_659_);
lean_dec_ref(v_e_656_);
lean_dec_ref(v_pattern_655_);
v_val_762_ = lean_ctor_get(v_fst_699_, 0);
lean_inc(v_val_762_);
lean_dec_ref(v_fst_699_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v_val_762_);
v___x_764_ = v___x_697_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_val_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v_a_685_);
lean_dec_ref(v_expr_659_);
lean_dec_ref(v_e_656_);
lean_dec_ref(v_pattern_655_);
v_a_767_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_694_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_694_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_del_object(v___x_681_);
lean_dec_ref(v_args_679_);
lean_dec_ref(v_expr_659_);
lean_dec_ref(v_d_658_);
lean_dec_ref(v_e_656_);
lean_dec_ref(v_pattern_655_);
v_a_776_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_684_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_684_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_787_; 
lean_dec(v_a_673_);
lean_dec_ref(v_expr_659_);
lean_dec_ref(v_d_658_);
lean_dec_ref(v_e_656_);
lean_dec_ref(v_pattern_655_);
v___x_785_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0));
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_785_);
v___x_787_ = v___x_675_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_dec_ref(v_expr_659_);
lean_dec_ref(v_d_658_);
lean_dec_ref(v_e_656_);
lean_dec_ref(v_pattern_655_);
v_a_790_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_672_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_672_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object** _args){
lean_object* v_pattern_798_ = _args[0];
lean_object* v_e_799_ = _args[1];
lean_object* v___x_800_ = _args[2];
lean_object* v_d_801_ = _args[3];
lean_object* v_expr_802_ = _args[4];
lean_object* v_rhs_803_ = _args[5];
lean_object* v_perm_804_ = _args[6];
lean_object* v___y_805_ = _args[7];
lean_object* v___y_806_ = _args[8];
lean_object* v___y_807_ = _args[9];
lean_object* v___y_808_ = _args[10];
lean_object* v___y_809_ = _args[11];
lean_object* v___y_810_ = _args[12];
lean_object* v___y_811_ = _args[13];
lean_object* v___y_812_ = _args[14];
lean_object* v___y_813_ = _args[15];
lean_object* v___y_814_ = _args[16];
_start:
{
uint8_t v___x_34686__boxed_815_; uint8_t v_perm_boxed_816_; lean_object* v_res_817_; 
v___x_34686__boxed_815_ = lean_unbox(v___x_800_);
v_perm_boxed_816_ = lean_unbox(v_perm_804_);
v_res_817_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(v_pattern_798_, v_e_799_, v___x_34686__boxed_815_, v_d_801_, v_expr_802_, v_rhs_803_, v_perm_boxed_816_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v_rhs_803_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object* v_thm_818_, lean_object* v_e_819_, lean_object* v_d_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_expr_831_; lean_object* v_pattern_832_; lean_object* v_rhs_833_; uint8_t v_perm_834_; uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___f_838_; uint8_t v___x_839_; lean_object* v___x_840_; 
v_expr_831_ = lean_ctor_get(v_thm_818_, 0);
lean_inc_ref(v_expr_831_);
v_pattern_832_ = lean_ctor_get(v_thm_818_, 1);
lean_inc_ref(v_pattern_832_);
v_rhs_833_ = lean_ctor_get(v_thm_818_, 2);
lean_inc_ref(v_rhs_833_);
v_perm_834_ = lean_ctor_get_uint8(v_thm_818_, sizeof(void*)*3);
lean_dec_ref(v_thm_818_);
v___x_835_ = 1;
v___x_836_ = lean_box(v___x_835_);
v___x_837_ = lean_box(v_perm_834_);
v___f_838_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed), 17, 7);
lean_closure_set(v___f_838_, 0, v_pattern_832_);
lean_closure_set(v___f_838_, 1, v_e_819_);
lean_closure_set(v___f_838_, 2, v___x_836_);
lean_closure_set(v___f_838_, 3, v_d_820_);
lean_closure_set(v___f_838_, 4, v_expr_831_);
lean_closure_set(v___f_838_, 5, v_rhs_833_);
lean_closure_set(v___f_838_, 6, v___x_837_);
v___x_839_ = 0;
v___x_840_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v___f_838_, v___x_839_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object* v_thm_841_, lean_object* v_e_842_, lean_object* v_d_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_thm_841_, v_e_842_, v_d_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(lean_object* v_mvarId_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_855_, v___y_862_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(lean_object* v_mvarId_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(v_mvarId_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec(v_mvarId_867_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(lean_object* v_mvarId_879_, lean_object* v_val_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_879_, v_val_880_, v___y_887_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(lean_object* v_mvarId_892_, lean_object* v_val_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(v_mvarId_892_, v_val_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(lean_object* v_upperBound_905_, lean_object* v_d_906_, lean_object* v___x_907_, lean_object* v_inst_908_, lean_object* v_R_909_, lean_object* v_a_910_, lean_object* v_b_911_, lean_object* v_c_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_upperBound_905_, v_d_906_, v_a_910_, v_b_911_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_924_ = _args[0];
lean_object* v_d_925_ = _args[1];
lean_object* v___x_926_ = _args[2];
lean_object* v_inst_927_ = _args[3];
lean_object* v_R_928_ = _args[4];
lean_object* v_a_929_ = _args[5];
lean_object* v_b_930_ = _args[6];
lean_object* v_c_931_ = _args[7];
lean_object* v___y_932_ = _args[8];
lean_object* v___y_933_ = _args[9];
lean_object* v___y_934_ = _args[10];
lean_object* v___y_935_ = _args[11];
lean_object* v___y_936_ = _args[12];
lean_object* v___y_937_ = _args[13];
lean_object* v___y_938_ = _args[14];
lean_object* v___y_939_ = _args[15];
lean_object* v___y_940_ = _args[16];
lean_object* v___y_941_ = _args[17];
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(v_upperBound_924_, v_d_925_, v___x_926_, v_inst_927_, v_R_928_, v_a_929_, v_b_930_, v_c_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec(v___x_926_);
lean_dec(v_upperBound_924_);
return v_res_942_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_object* v_00_u03b2_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
uint8_t v___x_946_; 
v___x_946_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_944_, v_x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(lean_object* v_00_u03b2_947_, lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
uint8_t v_res_950_; lean_object* v_r_951_; 
v_res_950_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(v_00_u03b2_947_, v_x_948_, v_x_949_);
lean_dec(v_x_949_);
lean_dec_ref(v_x_948_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(lean_object* v_00_u03b2_952_, lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_x_953_, v_x_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_957_, lean_object* v_x_958_, size_t v_x_959_, lean_object* v_x_960_){
_start:
{
uint8_t v___x_961_; 
v___x_961_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_958_, v_x_959_, v_x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_962_, lean_object* v_x_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
size_t v_x_35096__boxed_966_; uint8_t v_res_967_; lean_object* v_r_968_; 
v_x_35096__boxed_966_ = lean_unbox_usize(v_x_964_);
lean_dec(v_x_964_);
v_res_967_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(v_00_u03b2_962_, v_x_963_, v_x_35096__boxed_966_, v_x_965_);
lean_dec(v_x_965_);
lean_dec_ref(v_x_963_);
v_r_968_ = lean_box(v_res_967_);
return v_r_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_969_, lean_object* v_x_970_, size_t v_x_971_, size_t v_x_972_, lean_object* v_x_973_, lean_object* v_x_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_970_, v_x_971_, v_x_972_, v_x_973_, v_x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_976_, lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
size_t v_x_35107__boxed_982_; size_t v_x_35108__boxed_983_; lean_object* v_res_984_; 
v_x_35107__boxed_982_ = lean_unbox_usize(v_x_978_);
lean_dec(v_x_978_);
v_x_35108__boxed_983_ = lean_unbox_usize(v_x_979_);
lean_dec(v_x_979_);
v_res_984_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(v_00_u03b2_976_, v_x_977_, v_x_35107__boxed_982_, v_x_35108__boxed_983_, v_x_980_, v_x_981_);
return v_res_984_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_985_, lean_object* v_keys_986_, lean_object* v_vals_987_, lean_object* v_heq_988_, lean_object* v_i_989_, lean_object* v_k_990_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_keys_986_, v_i_989_, v_k_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_992_, lean_object* v_keys_993_, lean_object* v_vals_994_, lean_object* v_heq_995_, lean_object* v_i_996_, lean_object* v_k_997_){
_start:
{
uint8_t v_res_998_; lean_object* v_r_999_; 
v_res_998_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(v_00_u03b2_992_, v_keys_993_, v_vals_994_, v_heq_995_, v_i_996_, v_k_997_);
lean_dec(v_k_997_);
lean_dec_ref(v_vals_994_);
lean_dec_ref(v_keys_993_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_1000_, lean_object* v_n_1001_, lean_object* v_k_1002_, lean_object* v_v_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(v_n_1001_, v_k_1002_, v_v_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_1005_, size_t v_depth_1006_, lean_object* v_keys_1007_, lean_object* v_vals_1008_, lean_object* v_heq_1009_, lean_object* v_i_1010_, lean_object* v_entries_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_depth_1006_, v_keys_1007_, v_vals_1008_, v_i_1010_, v_entries_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1013_, lean_object* v_depth_1014_, lean_object* v_keys_1015_, lean_object* v_vals_1016_, lean_object* v_heq_1017_, lean_object* v_i_1018_, lean_object* v_entries_1019_){
_start:
{
size_t v_depth_boxed_1020_; lean_object* v_res_1021_; 
v_depth_boxed_1020_ = lean_unbox_usize(v_depth_1014_);
lean_dec(v_depth_1014_);
v_res_1021_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_1013_, v_depth_boxed_1020_, v_keys_1015_, v_vals_1016_, v_heq_1017_, v_i_1018_, v_entries_1019_);
lean_dec_ref(v_vals_1016_);
lean_dec_ref(v_keys_1015_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(v_x_1023_, v_x_1024_, v_x_1025_, v_x_1026_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(lean_object* v_fst_1028_, lean_object* v_d_1029_, lean_object* v_x_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1028_, v_x_1030_, v_d_1029_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed(lean_object* v_fst_1042_, lean_object* v_d_1043_, lean_object* v_x_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(v_fst_1042_, v_d_1043_, v_x_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object* v_d_1056_, lean_object* v_e_1057_, lean_object* v_as_1058_, size_t v_sz_1059_, size_t v_i_1060_, lean_object* v_b_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
uint8_t v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1080_; uint8_t v___y_1081_; uint8_t v___y_1082_; lean_object* v___y_1085_; uint8_t v___y_1086_; uint8_t v___y_1087_; uint8_t v___y_1088_; lean_object* v___y_1090_; uint8_t v___y_1091_; uint8_t v___y_1092_; lean_object* v___y_1096_; uint8_t v___y_1097_; uint8_t v___x_1099_; 
v___x_1099_ = lean_usize_dec_lt(v_i_1060_, v_sz_1059_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
lean_dec_ref(v_e_1057_);
lean_dec_ref(v_d_1056_);
v___x_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_b_1061_);
return v___x_1100_;
}
else
{
lean_object* v_a_1101_; lean_object* v_fst_1102_; lean_object* v_snd_1103_; lean_object* v_snd_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1153_; 
v_a_1101_ = lean_array_uget_borrowed(v_as_1058_, v_i_1060_);
v_fst_1102_ = lean_ctor_get(v_a_1101_, 0);
v_snd_1103_ = lean_ctor_get(v_a_1101_, 1);
v_snd_1104_ = lean_ctor_get(v_b_1061_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_b_1061_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v_b_1061_, 0);
lean_dec(v_unused_1154_);
v___x_1106_ = v_b_1061_;
v_isShared_1107_ = v_isSharedCheck_1153_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_snd_1104_);
lean_dec(v_b_1061_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1153_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___y_1110_; uint8_t v_done_1111_; uint8_t v___y_1112_; lean_object* v_result_1122_; lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1108_ = lean_box(0);
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_nat_dec_eq(v_snd_1103_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___f_1132_; lean_object* v___x_1133_; 
lean_inc_ref(v_d_1056_);
lean_inc(v_fst_1102_);
v___f_1132_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1132_, 0, v_fst_1102_);
lean_closure_set(v___f_1132_, 1, v_d_1056_);
lean_inc_ref(v_e_1057_);
v___x_1133_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_1057_, v_snd_1103_, v___f_1132_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref(v___x_1133_);
v_result_1122_ = v_a_1134_;
goto v___jp_1121_;
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_del_object(v___x_1106_);
lean_dec(v_snd_1104_);
lean_dec_ref(v_e_1057_);
lean_dec_ref(v_d_1056_);
v_a_1135_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1133_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_object* v___x_1143_; 
lean_inc_ref(v_d_1056_);
lean_inc_ref(v_e_1057_);
lean_inc(v_fst_1102_);
v___x_1143_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1102_, v_e_1057_, v_d_1056_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref(v___x_1143_);
v_result_1122_ = v_a_1144_;
goto v___jp_1121_;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_del_object(v___x_1106_);
lean_dec(v_snd_1104_);
lean_dec_ref(v_e_1057_);
lean_dec_ref(v_d_1056_);
v_a_1145_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1143_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
v___jp_1109_:
{
if (v_done_1111_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
lean_dec_ref(v___y_1110_);
v___x_1113_ = lean_box(v___y_1112_);
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 1, v___x_1113_);
lean_ctor_set(v___x_1106_, 0, v___x_1108_);
v___x_1115_ = v___x_1106_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1108_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
size_t v___x_1116_; size_t v___x_1117_; 
v___x_1116_ = ((size_t)1ULL);
v___x_1117_ = lean_usize_add(v_i_1060_, v___x_1116_);
v_i_1060_ = v___x_1117_;
v_b_1061_ = v___x_1115_;
goto _start;
}
}
else
{
uint8_t v___x_1120_; 
lean_del_object(v___x_1106_);
lean_dec_ref(v_e_1057_);
lean_dec_ref(v_d_1056_);
v___x_1120_ = 0;
v___y_1090_ = v___y_1110_;
v___y_1091_ = v___y_1112_;
v___y_1092_ = v___x_1120_;
goto v___jp_1089_;
}
}
v___jp_1121_:
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_unbox(v_snd_1104_);
if (v___x_1123_ == 0)
{
lean_dec(v_snd_1104_);
if (lean_obj_tag(v_result_1122_) == 0)
{
uint8_t v_done_1124_; uint8_t v_contextDependent_1125_; 
v_done_1124_ = lean_ctor_get_uint8(v_result_1122_, 0);
v_contextDependent_1125_ = lean_ctor_get_uint8(v_result_1122_, 1);
v___y_1110_ = v_result_1122_;
v_done_1111_ = v_done_1124_;
v___y_1112_ = v_contextDependent_1125_;
goto v___jp_1109_;
}
else
{
uint8_t v_contextDependent_1126_; 
lean_del_object(v___x_1106_);
lean_dec_ref(v_e_1057_);
lean_dec_ref(v_d_1056_);
v_contextDependent_1126_ = lean_ctor_get_uint8(v_result_1122_, sizeof(void*)*2 + 1);
v___y_1096_ = v_result_1122_;
v___y_1097_ = v_contextDependent_1126_;
goto v___jp_1095_;
}
}
else
{
if (lean_obj_tag(v_result_1122_) == 0)
{
uint8_t v_done_1127_; uint8_t v___x_1128_; 
v_done_1127_ = lean_ctor_get_uint8(v_result_1122_, 0);
v___x_1128_ = lean_unbox(v_snd_1104_);
lean_dec(v_snd_1104_);
v___y_1110_ = v_result_1122_;
v_done_1111_ = v_done_1127_;
v___y_1112_ = v___x_1128_;
goto v___jp_1109_;
}
else
{
uint8_t v___x_1129_; 
lean_del_object(v___x_1106_);
lean_dec_ref(v_e_1057_);
lean_dec_ref(v_d_1056_);
v___x_1129_ = lean_unbox(v_snd_1104_);
lean_dec(v_snd_1104_);
v___y_1096_ = v_result_1122_;
v___y_1097_ = v___x_1129_;
goto v___jp_1095_;
}
}
}
}
}
v___jp_1072_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___y_1074_);
v___x_1076_ = lean_box(v___y_1073_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
v___jp_1079_:
{
if (v___y_1082_ == 0)
{
v___y_1073_ = v___y_1081_;
v___y_1074_ = v___y_1080_;
goto v___jp_1072_;
}
else
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1080_);
v___y_1073_ = v___y_1081_;
v___y_1074_ = v___x_1083_;
goto v___jp_1072_;
}
}
v___jp_1084_:
{
if (v___y_1088_ == 0)
{
v___y_1080_ = v___y_1085_;
v___y_1081_ = v___y_1087_;
v___y_1082_ = v___y_1087_;
goto v___jp_1079_;
}
else
{
v___y_1080_ = v___y_1085_;
v___y_1081_ = v___y_1087_;
v___y_1082_ = v___y_1086_;
goto v___jp_1079_;
}
}
v___jp_1089_:
{
if (v___y_1091_ == 0)
{
v___y_1073_ = v___y_1091_;
v___y_1074_ = v___y_1090_;
goto v___jp_1072_;
}
else
{
if (lean_obj_tag(v___y_1090_) == 0)
{
uint8_t v_contextDependent_1093_; 
v_contextDependent_1093_ = lean_ctor_get_uint8(v___y_1090_, 1);
v___y_1085_ = v___y_1090_;
v___y_1086_ = v___y_1092_;
v___y_1087_ = v___y_1091_;
v___y_1088_ = v_contextDependent_1093_;
goto v___jp_1084_;
}
else
{
uint8_t v_contextDependent_1094_; 
v_contextDependent_1094_ = lean_ctor_get_uint8(v___y_1090_, sizeof(void*)*2 + 1);
v___y_1085_ = v___y_1090_;
v___y_1086_ = v___y_1092_;
v___y_1087_ = v___y_1091_;
v___y_1088_ = v_contextDependent_1094_;
goto v___jp_1084_;
}
}
}
v___jp_1095_:
{
uint8_t v___x_1098_; 
v___x_1098_ = 0;
v___y_1090_ = v___y_1096_;
v___y_1091_ = v___y_1097_;
v___y_1092_ = v___x_1098_;
goto v___jp_1089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object* v_d_1155_, lean_object* v_e_1156_, lean_object* v_as_1157_, lean_object* v_sz_1158_, lean_object* v_i_1159_, lean_object* v_b_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
size_t v_sz_boxed_1171_; size_t v_i_boxed_1172_; lean_object* v_res_1173_; 
v_sz_boxed_1171_ = lean_unbox_usize(v_sz_1158_);
lean_dec(v_sz_1158_);
v_i_boxed_1172_ = lean_unbox_usize(v_i_1159_);
lean_dec(v_i_1159_);
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1155_, v_e_1156_, v_as_1157_, v_sz_boxed_1171_, v_i_boxed_1172_, v_b_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v_as_1157_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object* v_thms_1178_, lean_object* v_d_1179_, lean_object* v_e_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; size_t v_sz_1193_; size_t v___x_1194_; lean_object* v___x_1195_; 
v___x_1191_ = l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(v_thms_1178_, v_e_1180_);
v___x_1192_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0));
v_sz_1193_ = lean_array_size(v___x_1191_);
v___x_1194_ = ((size_t)0ULL);
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1179_, v_e_1180_, v___x_1191_, v_sz_1193_, v___x_1194_, v___x_1192_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
lean_dec_ref(v___x_1191_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1211_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1211_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1211_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v_fst_1200_; 
v_fst_1200_ = lean_ctor_get(v_a_1196_, 0);
if (lean_obj_tag(v_fst_1200_) == 0)
{
lean_object* v_snd_1201_; uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v_snd_1201_ = lean_ctor_get(v_a_1196_, 1);
lean_inc(v_snd_1201_);
lean_dec(v_a_1196_);
v___x_1202_ = lean_unbox(v_snd_1201_);
lean_dec(v_snd_1201_);
v___x_1203_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1202_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1203_);
v___x_1205_ = v___x_1198_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
else
{
lean_object* v_val_1207_; lean_object* v___x_1209_; 
lean_inc_ref(v_fst_1200_);
lean_dec(v_a_1196_);
v_val_1207_ = lean_ctor_get(v_fst_1200_, 0);
lean_inc(v_val_1207_);
lean_dec_ref(v_fst_1200_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v_val_1207_);
v___x_1209_ = v___x_1198_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_val_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
v_a_1212_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1195_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1195_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object* v_thms_1220_, lean_object* v_d_1221_, lean_object* v_e_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_thms_1220_, v_d_1221_, v_e_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
return v_res_1233_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_ACLt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ACLt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* initialize_Lean_Meta_ACLt(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ACLt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
}
#ifdef __cplusplus
}
#endif
