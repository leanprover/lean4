// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Rewrite
// Imports: public import Lean.Meta.Sym.Simp.Simproc public import Lean.Meta.Sym.Simp.Theorems public import Lean.Meta.Sym.Simp.App public import Lean.Meta.Sym.Simp.Discharger import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InstantiateMVarsS import Init.Data.Range.Polymorphic.Iterators
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(lean_object* v_l_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; lean_object* v_mctx_22_; lean_object* v___x_23_; lean_object* v_fst_24_; lean_object* v_snd_25_; lean_object* v___x_26_; lean_object* v_cache_27_; lean_object* v_zetaDeltaFVarIds_28_; lean_object* v_postponed_29_; lean_object* v_diag_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_39_; 
v___x_21_ = lean_st_ref_get(v___y_19_);
v_mctx_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc_ref(v_mctx_22_);
lean_dec(v___x_21_);
v___x_23_ = lean_instantiate_level_mvars(v_mctx_22_, v_l_18_);
v_fst_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_fst_24_);
v_snd_25_ = lean_ctor_get(v___x_23_, 1);
lean_inc(v_snd_25_);
lean_dec_ref(v___x_23_);
v___x_26_ = lean_st_ref_take(v___y_19_);
v_cache_27_ = lean_ctor_get(v___x_26_, 1);
v_zetaDeltaFVarIds_28_ = lean_ctor_get(v___x_26_, 2);
v_postponed_29_ = lean_ctor_get(v___x_26_, 3);
v_diag_30_ = lean_ctor_get(v___x_26_, 4);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_26_);
if (v_isSharedCheck_39_ == 0)
{
lean_object* v_unused_40_; 
v_unused_40_ = lean_ctor_get(v___x_26_, 0);
lean_dec(v_unused_40_);
v___x_32_ = v___x_26_;
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_diag_30_);
lean_inc(v_postponed_29_);
lean_inc(v_zetaDeltaFVarIds_28_);
lean_inc(v_cache_27_);
lean_dec(v___x_26_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_35_; 
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v_fst_24_);
v___x_35_ = v___x_32_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_fst_24_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_cache_27_);
lean_ctor_set(v_reuseFailAlloc_38_, 2, v_zetaDeltaFVarIds_28_);
lean_ctor_set(v_reuseFailAlloc_38_, 3, v_postponed_29_);
lean_ctor_set(v_reuseFailAlloc_38_, 4, v_diag_30_);
v___x_35_ = v_reuseFailAlloc_38_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_st_ref_set(v___y_19_, v___x_35_);
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v_snd_25_);
return v___x_37_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg___boxed(lean_object* v_l_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_l_41_, v___y_42_);
lean_dec(v___y_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(lean_object* v_l_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_l_45_, v___y_52_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___boxed(lean_object* v_l_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(v_l_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(lean_object* v_k_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_apply_10(v_k_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, lean_box(0));
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed(lean_object* v_k_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_k_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(lean_object* v_k_93_, uint8_t v_allowLevelAssignments_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___f_105_; lean_object* v___x_106_; 
v___f_105_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_105_, 0, v_k_93_);
lean_closure_set(v___f_105_, 1, v___y_95_);
lean_closure_set(v___f_105_, 2, v___y_96_);
lean_closure_set(v___f_105_, 3, v___y_97_);
lean_closure_set(v___f_105_, 4, v___y_98_);
lean_closure_set(v___f_105_, 5, v___y_99_);
v___x_106_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_94_, v___f_105_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_106_) == 0)
{
return v___x_106_;
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___boxed(lean_object* v_k_115_, lean_object* v_allowLevelAssignments_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_127_; lean_object* v_res_128_; 
v_allowLevelAssignments_boxed_127_ = lean_unbox(v_allowLevelAssignments_116_);
v_res_128_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_k_115_, v_allowLevelAssignments_boxed_127_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(lean_object* v_00_u03b1_129_, lean_object* v_k_130_, uint8_t v_allowLevelAssignments_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_k_130_, v_allowLevelAssignments_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___boxed(lean_object* v_00_u03b1_143_, lean_object* v_k_144_, lean_object* v_allowLevelAssignments_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_156_; lean_object* v_res_157_; 
v_allowLevelAssignments_boxed_156_ = lean_unbox(v_allowLevelAssignments_145_);
v_res_157_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(v_00_u03b1_143_, v_k_144_, v_allowLevelAssignments_boxed_156_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = l_List_reverse___redArg(v_x_159_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
else
{
lean_object* v_head_172_; lean_object* v_tail_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_183_; 
v_head_172_ = lean_ctor_get(v_x_158_, 0);
v_tail_173_ = lean_ctor_get(v_x_158_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_183_ == 0)
{
v___x_175_ = v_x_158_;
v_isShared_176_ = v_isSharedCheck_183_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_tail_173_);
lean_inc(v_head_172_);
lean_dec(v_x_158_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_183_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v_a_178_; lean_object* v___x_180_; 
v___x_177_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_head_172_, v___y_166_);
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref(v___x_177_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v_x_159_);
lean_ctor_set(v___x_175_, 0, v_a_178_);
v___x_180_ = v___x_175_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_178_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_x_159_);
v___x_180_ = v_reuseFailAlloc_182_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
v_x_158_ = v_tail_173_;
v_x_159_ = v___x_180_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1___boxed(lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_x_184_, v_x_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
lean_object* v_ks_201_; lean_object* v_vs_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_226_; 
v_ks_201_ = lean_ctor_get(v_x_197_, 0);
v_vs_202_ = lean_ctor_get(v_x_197_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_197_);
if (v_isSharedCheck_226_ == 0)
{
v___x_204_ = v_x_197_;
v_isShared_205_ = v_isSharedCheck_226_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_vs_202_);
lean_inc(v_ks_201_);
lean_dec(v_x_197_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_226_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_206_ = lean_array_get_size(v_ks_201_);
v___x_207_ = lean_nat_dec_lt(v_x_198_, v___x_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
lean_dec(v_x_198_);
v___x_208_ = lean_array_push(v_ks_201_, v_x_199_);
v___x_209_ = lean_array_push(v_vs_202_, v_x_200_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_209_);
lean_ctor_set(v___x_204_, 0, v___x_208_);
v___x_211_ = v___x_204_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
else
{
lean_object* v_k_x27_213_; uint8_t v___x_214_; 
v_k_x27_213_ = lean_array_fget_borrowed(v_ks_201_, v_x_198_);
v___x_214_ = l_Lean_instBEqMVarId_beq(v_x_199_, v_k_x27_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_216_; 
if (v_isShared_205_ == 0)
{
v___x_216_ = v___x_204_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_ks_201_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_vs_202_);
v___x_216_ = v_reuseFailAlloc_220_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lean_nat_add(v_x_198_, v___x_217_);
lean_dec(v_x_198_);
v_x_197_ = v___x_216_;
v_x_198_ = v___x_218_;
goto _start;
}
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_221_ = lean_array_fset(v_ks_201_, v_x_198_, v_x_199_);
v___x_222_ = lean_array_fset(v_vs_202_, v_x_198_, v_x_200_);
lean_dec(v_x_198_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_222_);
lean_ctor_set(v___x_204_, 0, v___x_221_);
v___x_224_ = v___x_204_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_221_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_n_227_, lean_object* v_k_228_, lean_object* v_v_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(v_n_227_, v___x_230_, v_k_228_, v_v_229_);
return v___x_231_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0(void){
_start:
{
size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; 
v___x_232_ = ((size_t)5ULL);
v___x_233_ = ((size_t)1ULL);
v___x_234_ = lean_usize_shift_left(v___x_233_, v___x_232_);
return v___x_234_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1(void){
_start:
{
size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; 
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0);
v___x_237_ = lean_usize_sub(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2(void){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(lean_object* v_x_239_, size_t v_x_240_, size_t v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
lean_object* v_es_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v_j_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_es_244_ = lean_ctor_get(v_x_239_, 0);
v___x_245_ = ((size_t)5ULL);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1);
v___x_248_ = lean_usize_land(v_x_240_, v___x_247_);
v_j_249_ = lean_usize_to_nat(v___x_248_);
v___x_250_ = lean_array_get_size(v_es_244_);
v___x_251_ = lean_nat_dec_lt(v_j_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec(v_j_249_);
lean_dec(v_x_243_);
lean_dec(v_x_242_);
return v_x_239_;
}
else
{
lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_288_; 
lean_inc_ref(v_es_244_);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_239_);
if (v_isSharedCheck_288_ == 0)
{
lean_object* v_unused_289_; 
v_unused_289_ = lean_ctor_get(v_x_239_, 0);
lean_dec(v_unused_289_);
v___x_253_ = v_x_239_;
v_isShared_254_ = v_isSharedCheck_288_;
goto v_resetjp_252_;
}
else
{
lean_dec(v_x_239_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_288_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v_v_255_; lean_object* v___x_256_; lean_object* v_xs_x27_257_; lean_object* v___y_259_; 
v_v_255_ = lean_array_fget(v_es_244_, v_j_249_);
v___x_256_ = lean_box(0);
v_xs_x27_257_ = lean_array_fset(v_es_244_, v_j_249_, v___x_256_);
switch(lean_obj_tag(v_v_255_))
{
case 0:
{
lean_object* v_key_264_; lean_object* v_val_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_275_; 
v_key_264_ = lean_ctor_get(v_v_255_, 0);
v_val_265_ = lean_ctor_get(v_v_255_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_v_255_);
if (v_isSharedCheck_275_ == 0)
{
v___x_267_ = v_v_255_;
v_isShared_268_ = v_isSharedCheck_275_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_val_265_);
lean_inc(v_key_264_);
lean_dec(v_v_255_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_275_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
uint8_t v___x_269_; 
v___x_269_ = l_Lean_instBEqMVarId_beq(v_x_242_, v_key_264_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_del_object(v___x_267_);
v___x_270_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_264_, v_val_265_, v_x_242_, v_x_243_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
v___y_259_ = v___x_271_;
goto v___jp_258_;
}
else
{
lean_object* v___x_273_; 
lean_dec(v_val_265_);
lean_dec(v_key_264_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v_x_243_);
lean_ctor_set(v___x_267_, 0, v_x_242_);
v___x_273_ = v___x_267_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_x_242_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_x_243_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
v___y_259_ = v___x_273_;
goto v___jp_258_;
}
}
}
}
case 1:
{
lean_object* v_node_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_286_; 
v_node_276_ = lean_ctor_get(v_v_255_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_v_255_);
if (v_isSharedCheck_286_ == 0)
{
v___x_278_ = v_v_255_;
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_node_276_);
lean_dec(v_v_255_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_286_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_280_ = lean_usize_shift_right(v_x_240_, v___x_245_);
v___x_281_ = lean_usize_add(v_x_241_, v___x_246_);
v___x_282_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_node_276_, v___x_280_, v___x_281_, v_x_242_, v_x_243_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_282_);
v___x_284_ = v___x_278_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
v___y_259_ = v___x_284_;
goto v___jp_258_;
}
}
}
default: 
{
lean_object* v___x_287_; 
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v_x_242_);
lean_ctor_set(v___x_287_, 1, v_x_243_);
v___y_259_ = v___x_287_;
goto v___jp_258_;
}
}
v___jp_258_:
{
lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_260_ = lean_array_fset(v_xs_x27_257_, v_j_249_, v___y_259_);
lean_dec(v_j_249_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_260_);
v___x_262_ = v___x_253_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
else
{
lean_object* v_ks_290_; lean_object* v_vs_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_311_; 
v_ks_290_ = lean_ctor_get(v_x_239_, 0);
v_vs_291_ = lean_ctor_get(v_x_239_, 1);
v_isSharedCheck_311_ = !lean_is_exclusive(v_x_239_);
if (v_isSharedCheck_311_ == 0)
{
v___x_293_ = v_x_239_;
v_isShared_294_ = v_isSharedCheck_311_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_vs_291_);
lean_inc(v_ks_290_);
lean_dec(v_x_239_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_311_;
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
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_ks_290_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_vs_291_);
v___x_296_ = v_reuseFailAlloc_310_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v_newNode_297_; uint8_t v___y_299_; size_t v___x_305_; uint8_t v___x_306_; 
v_newNode_297_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(v___x_296_, v_x_242_, v_x_243_);
v___x_305_ = ((size_t)7ULL);
v___x_306_ = lean_usize_dec_le(v___x_305_, v_x_241_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_297_);
v___x_308_ = lean_unsigned_to_nat(4u);
v___x_309_ = lean_nat_dec_lt(v___x_307_, v___x_308_);
lean_dec(v___x_307_);
v___y_299_ = v___x_309_;
goto v___jp_298_;
}
else
{
v___y_299_ = v___x_306_;
goto v___jp_298_;
}
v___jp_298_:
{
if (v___y_299_ == 0)
{
lean_object* v_ks_300_; lean_object* v_vs_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v_ks_300_ = lean_ctor_get(v_newNode_297_, 0);
lean_inc_ref(v_ks_300_);
v_vs_301_ = lean_ctor_get(v_newNode_297_, 1);
lean_inc_ref(v_vs_301_);
lean_dec_ref(v_newNode_297_);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__2);
v___x_304_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_x_241_, v_ks_300_, v_vs_301_, v___x_302_, v___x_303_);
lean_dec_ref(v_vs_301_);
lean_dec_ref(v_ks_300_);
return v___x_304_;
}
else
{
return v_newNode_297_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(size_t v_depth_312_, lean_object* v_keys_313_, lean_object* v_vals_314_, lean_object* v_i_315_, lean_object* v_entries_316_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_array_get_size(v_keys_313_);
v___x_318_ = lean_nat_dec_lt(v_i_315_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v_i_315_);
return v_entries_316_;
}
else
{
lean_object* v_k_319_; lean_object* v_v_320_; uint64_t v___x_321_; size_t v_h_322_; size_t v___x_323_; lean_object* v___x_324_; size_t v___x_325_; size_t v___x_326_; size_t v___x_327_; size_t v_h_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_k_319_ = lean_array_fget_borrowed(v_keys_313_, v_i_315_);
v_v_320_ = lean_array_fget_borrowed(v_vals_314_, v_i_315_);
v___x_321_ = l_Lean_instHashableMVarId_hash(v_k_319_);
v_h_322_ = lean_uint64_to_usize(v___x_321_);
v___x_323_ = ((size_t)5ULL);
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = ((size_t)1ULL);
v___x_326_ = lean_usize_sub(v_depth_312_, v___x_325_);
v___x_327_ = lean_usize_mul(v___x_323_, v___x_326_);
v_h_328_ = lean_usize_shift_right(v_h_322_, v___x_327_);
v___x_329_ = lean_nat_add(v_i_315_, v___x_324_);
lean_dec(v_i_315_);
lean_inc(v_v_320_);
lean_inc(v_k_319_);
v___x_330_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_entries_316_, v_h_328_, v_depth_312_, v_k_319_, v_v_320_);
v_i_315_ = v___x_329_;
v_entries_316_ = v___x_330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_depth_332_, lean_object* v_keys_333_, lean_object* v_vals_334_, lean_object* v_i_335_, lean_object* v_entries_336_){
_start:
{
size_t v_depth_boxed_337_; lean_object* v_res_338_; 
v_depth_boxed_337_ = lean_unbox_usize(v_depth_332_);
lean_dec(v_depth_332_);
v_res_338_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_depth_boxed_337_, v_keys_333_, v_vals_334_, v_i_335_, v_entries_336_);
lean_dec_ref(v_vals_334_);
lean_dec_ref(v_keys_333_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v_x_343_){
_start:
{
size_t v_x_31604__boxed_344_; size_t v_x_31605__boxed_345_; lean_object* v_res_346_; 
v_x_31604__boxed_344_ = lean_unbox_usize(v_x_340_);
lean_dec(v_x_340_);
v_x_31605__boxed_345_ = lean_unbox_usize(v_x_341_);
lean_dec(v_x_341_);
v_res_346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_339_, v_x_31604__boxed_344_, v_x_31605__boxed_345_, v_x_342_, v_x_343_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
uint64_t v___x_350_; size_t v___x_351_; size_t v___x_352_; lean_object* v___x_353_; 
v___x_350_ = l_Lean_instHashableMVarId_hash(v_x_348_);
v___x_351_ = lean_uint64_to_usize(v___x_350_);
v___x_352_ = ((size_t)1ULL);
v___x_353_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_347_, v___x_351_, v___x_352_, v_x_348_, v_x_349_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(lean_object* v_mvarId_354_, lean_object* v_val_355_, lean_object* v___y_356_){
_start:
{
lean_object* v___x_358_; lean_object* v_mctx_359_; lean_object* v_cache_360_; lean_object* v_zetaDeltaFVarIds_361_; lean_object* v_postponed_362_; lean_object* v_diag_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_390_; 
v___x_358_ = lean_st_ref_take(v___y_356_);
v_mctx_359_ = lean_ctor_get(v___x_358_, 0);
v_cache_360_ = lean_ctor_get(v___x_358_, 1);
v_zetaDeltaFVarIds_361_ = lean_ctor_get(v___x_358_, 2);
v_postponed_362_ = lean_ctor_get(v___x_358_, 3);
v_diag_363_ = lean_ctor_get(v___x_358_, 4);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_390_ == 0)
{
v___x_365_ = v___x_358_;
v_isShared_366_ = v_isSharedCheck_390_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_diag_363_);
lean_inc(v_postponed_362_);
lean_inc(v_zetaDeltaFVarIds_361_);
lean_inc(v_cache_360_);
lean_inc(v_mctx_359_);
lean_dec(v___x_358_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_390_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v_depth_367_; lean_object* v_levelAssignDepth_368_; lean_object* v_mvarCounter_369_; lean_object* v_lDepth_370_; lean_object* v_decls_371_; lean_object* v_userNames_372_; lean_object* v_lAssignment_373_; lean_object* v_eAssignment_374_; lean_object* v_dAssignment_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_389_; 
v_depth_367_ = lean_ctor_get(v_mctx_359_, 0);
v_levelAssignDepth_368_ = lean_ctor_get(v_mctx_359_, 1);
v_mvarCounter_369_ = lean_ctor_get(v_mctx_359_, 2);
v_lDepth_370_ = lean_ctor_get(v_mctx_359_, 3);
v_decls_371_ = lean_ctor_get(v_mctx_359_, 4);
v_userNames_372_ = lean_ctor_get(v_mctx_359_, 5);
v_lAssignment_373_ = lean_ctor_get(v_mctx_359_, 6);
v_eAssignment_374_ = lean_ctor_get(v_mctx_359_, 7);
v_dAssignment_375_ = lean_ctor_get(v_mctx_359_, 8);
v_isSharedCheck_389_ = !lean_is_exclusive(v_mctx_359_);
if (v_isSharedCheck_389_ == 0)
{
v___x_377_ = v_mctx_359_;
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_dAssignment_375_);
lean_inc(v_eAssignment_374_);
lean_inc(v_lAssignment_373_);
lean_inc(v_userNames_372_);
lean_inc(v_decls_371_);
lean_inc(v_lDepth_370_);
lean_inc(v_mvarCounter_369_);
lean_inc(v_levelAssignDepth_368_);
lean_inc(v_depth_367_);
lean_dec(v_mctx_359_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_389_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_eAssignment_374_, v_mvarId_354_, v_val_355_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 7, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_depth_367_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_levelAssignDepth_368_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_mvarCounter_369_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v_lDepth_370_);
lean_ctor_set(v_reuseFailAlloc_388_, 4, v_decls_371_);
lean_ctor_set(v_reuseFailAlloc_388_, 5, v_userNames_372_);
lean_ctor_set(v_reuseFailAlloc_388_, 6, v_lAssignment_373_);
lean_ctor_set(v_reuseFailAlloc_388_, 7, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_388_, 8, v_dAssignment_375_);
v___x_381_ = v_reuseFailAlloc_388_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_383_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_381_);
v___x_383_ = v___x_365_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_381_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_cache_360_);
lean_ctor_set(v_reuseFailAlloc_387_, 2, v_zetaDeltaFVarIds_361_);
lean_ctor_set(v_reuseFailAlloc_387_, 3, v_postponed_362_);
lean_ctor_set(v_reuseFailAlloc_387_, 4, v_diag_363_);
v___x_383_ = v_reuseFailAlloc_387_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_st_ref_set(v___y_356_, v___x_383_);
v___x_385_ = lean_box(0);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(lean_object* v_mvarId_391_, lean_object* v_val_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_391_, v_val_392_, v___y_393_);
lean_dec(v___y_393_);
return v_res_395_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_keys_396_, lean_object* v_i_397_, lean_object* v_k_398_){
_start:
{
lean_object* v___x_399_; uint8_t v___x_400_; 
v___x_399_ = lean_array_get_size(v_keys_396_);
v___x_400_ = lean_nat_dec_lt(v_i_397_, v___x_399_);
if (v___x_400_ == 0)
{
lean_dec(v_i_397_);
return v___x_400_;
}
else
{
lean_object* v_k_x27_401_; uint8_t v___x_402_; 
v_k_x27_401_ = lean_array_fget_borrowed(v_keys_396_, v_i_397_);
v___x_402_ = l_Lean_instBEqMVarId_beq(v_k_398_, v_k_x27_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(1u);
v___x_404_ = lean_nat_add(v_i_397_, v___x_403_);
lean_dec(v_i_397_);
v_i_397_ = v___x_404_;
goto _start;
}
else
{
lean_dec(v_i_397_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_keys_406_, lean_object* v_i_407_, lean_object* v_k_408_){
_start:
{
uint8_t v_res_409_; lean_object* v_r_410_; 
v_res_409_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_keys_406_, v_i_407_, v_k_408_);
lean_dec(v_k_408_);
lean_dec_ref(v_keys_406_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(lean_object* v_x_411_, size_t v_x_412_, lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_411_) == 0)
{
lean_object* v_es_414_; lean_object* v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; lean_object* v_j_419_; lean_object* v___x_420_; 
v_es_414_ = lean_ctor_get(v_x_411_, 0);
lean_inc_ref(v_es_414_);
lean_dec_ref(v_x_411_);
v___x_415_ = lean_box(2);
v___x_416_ = ((size_t)5ULL);
v___x_417_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__1);
v___x_418_ = lean_usize_land(v_x_412_, v___x_417_);
v_j_419_ = lean_usize_to_nat(v___x_418_);
v___x_420_ = lean_array_get(v___x_415_, v_es_414_, v_j_419_);
lean_dec(v_j_419_);
lean_dec_ref(v_es_414_);
switch(lean_obj_tag(v___x_420_))
{
case 0:
{
lean_object* v_key_421_; uint8_t v___x_422_; 
v_key_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_key_421_);
lean_dec_ref(v___x_420_);
v___x_422_ = l_Lean_instBEqMVarId_beq(v_x_413_, v_key_421_);
lean_dec(v_key_421_);
return v___x_422_;
}
case 1:
{
lean_object* v_node_423_; size_t v___x_424_; 
v_node_423_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_node_423_);
lean_dec_ref(v___x_420_);
v___x_424_ = lean_usize_shift_right(v_x_412_, v___x_416_);
v_x_411_ = v_node_423_;
v_x_412_ = v___x_424_;
goto _start;
}
default: 
{
uint8_t v___x_426_; 
v___x_426_ = 0;
return v___x_426_;
}
}
}
else
{
lean_object* v_ks_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v_ks_427_ = lean_ctor_get(v_x_411_, 0);
lean_inc_ref(v_ks_427_);
lean_dec_ref(v_x_411_);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_ks_427_, v___x_428_, v_x_413_);
lean_dec_ref(v_ks_427_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
size_t v_x_31842__boxed_433_; uint8_t v_res_434_; lean_object* v_r_435_; 
v_x_31842__boxed_433_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_res_434_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_430_, v_x_31842__boxed_433_, v_x_432_);
lean_dec(v_x_432_);
v_r_435_ = lean_box(v_res_434_);
return v_r_435_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
uint64_t v___x_438_; size_t v___x_439_; uint8_t v___x_440_; 
v___x_438_ = l_Lean_instHashableMVarId_hash(v_x_437_);
v___x_439_ = lean_uint64_to_usize(v___x_438_);
v___x_440_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_436_, v___x_439_, v_x_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg___boxed(lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
uint8_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_441_, v_x_442_);
lean_dec(v_x_442_);
v_r_444_ = lean_box(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(lean_object* v_mvarId_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; lean_object* v_mctx_449_; lean_object* v_eAssignment_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = lean_st_ref_get(v___y_446_);
v_mctx_449_ = lean_ctor_get(v___x_448_, 0);
lean_inc_ref(v_mctx_449_);
lean_dec(v___x_448_);
v_eAssignment_450_ = lean_ctor_get(v_mctx_449_, 7);
lean_inc_ref(v_eAssignment_450_);
lean_dec_ref(v_mctx_449_);
v___x_451_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_eAssignment_450_, v_mvarId_445_);
v___x_452_ = lean_box(v___x_451_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg___boxed(lean_object* v_mvarId_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec(v_mvarId_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(lean_object* v_upperBound_458_, lean_object* v_d_459_, lean_object* v_a_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_a_473_; uint8_t v___x_477_; 
v___x_477_ = lean_nat_dec_lt(v_a_460_, v_upperBound_458_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v_a_460_);
lean_dec_ref(v_d_459_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_b_461_);
return v___x_478_;
}
else
{
lean_object* v_snd_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_613_; 
v_snd_479_ = lean_ctor_get(v_b_461_, 1);
v_isSharedCheck_613_ = !lean_is_exclusive(v_b_461_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v_b_461_, 0);
lean_dec(v_unused_614_);
v___x_481_ = v_b_461_;
v_isShared_482_ = v_isSharedCheck_613_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_snd_479_);
lean_dec(v_b_461_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_613_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v_fst_483_; lean_object* v_snd_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_612_; 
v_fst_483_ = lean_ctor_get(v_snd_479_, 0);
v_snd_484_ = lean_ctor_get(v_snd_479_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_snd_479_);
if (v_isSharedCheck_612_ == 0)
{
v___x_486_ = v_snd_479_;
v_isShared_487_ = v_isSharedCheck_612_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_snd_484_);
lean_inc(v_fst_483_);
lean_dec(v_snd_479_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_612_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_box(0);
v___x_489_ = lean_array_fget_borrowed(v_fst_483_, v_a_460_);
if (lean_obj_tag(v___x_489_) == 2)
{
lean_object* v_mvarId_490_; lean_object* v___x_491_; 
v_mvarId_490_ = lean_ctor_get(v___x_489_, 0);
v___x_491_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_490_, v___y_468_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; uint8_t v___x_493_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref(v___x_491_);
v___x_493_ = lean_unbox(v_a_492_);
lean_dec(v_a_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; 
lean_inc(v_mvarId_490_);
v___x_494_ = l_Lean_MVarId_getDecl(v_mvarId_490_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v_type_496_; lean_object* v___x_497_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref(v___x_494_);
v_type_496_ = lean_ctor_get(v_a_495_, 2);
lean_inc_ref(v_type_496_);
lean_dec(v_a_495_);
lean_inc_ref(v_d_459_);
lean_inc(v___y_470_);
lean_inc_ref(v___y_469_);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
lean_inc(v___y_462_);
v___x_497_ = lean_apply_11(v_d_459_, v_type_496_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, lean_box(0));
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_546_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_546_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_546_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_546_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint8_t v___y_503_; 
if (lean_obj_tag(v_a_498_) == 0)
{
uint8_t v___x_516_; 
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v_a_460_);
lean_dec_ref(v_d_459_);
v___x_516_ = lean_unbox(v_snd_484_);
lean_dec(v_snd_484_);
if (v___x_516_ == 0)
{
uint8_t v_contextDependent_517_; 
v_contextDependent_517_ = lean_ctor_get_uint8(v_a_498_, 0);
lean_dec_ref(v_a_498_);
v___y_503_ = v_contextDependent_517_;
goto v___jp_502_;
}
else
{
lean_dec_ref(v_a_498_);
v___y_503_ = v___x_477_;
goto v___jp_502_;
}
}
else
{
lean_object* v_proof_518_; uint8_t v_contextDependent_519_; uint8_t v___y_521_; uint8_t v___x_545_; 
lean_del_object(v___x_500_);
lean_del_object(v___x_486_);
lean_del_object(v___x_481_);
v_proof_518_ = lean_ctor_get(v_a_498_, 0);
lean_inc_ref(v_proof_518_);
v_contextDependent_519_ = lean_ctor_get_uint8(v_a_498_, sizeof(void*)*1);
lean_dec_ref(v_a_498_);
v___x_545_ = lean_unbox(v_snd_484_);
lean_dec(v_snd_484_);
if (v___x_545_ == 0)
{
v___y_521_ = v_contextDependent_519_;
goto v___jp_520_;
}
else
{
v___y_521_ = v___x_477_;
goto v___jp_520_;
}
v___jp_520_:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Meta_Sym_instantiateMVarsS(v_proof_518_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref(v___x_522_);
lean_inc(v_a_523_);
lean_inc(v_mvarId_490_);
v___x_524_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_490_, v_a_523_, v___y_468_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec_ref(v___x_524_);
v___x_525_ = lean_array_fset(v_fst_483_, v_a_460_, v_a_523_);
v___x_526_ = lean_box(v___y_521_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_488_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v_a_473_ = v___x_528_;
goto v___jp_472_;
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec(v_a_523_);
lean_dec(v_fst_483_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v_a_460_);
lean_dec_ref(v_d_459_);
v_a_529_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_524_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_524_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_dec(v_fst_483_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v_a_460_);
lean_dec_ref(v_d_459_);
v_a_537_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_522_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_522_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
v___jp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_504_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_503_);
v___x_505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
v___x_506_ = lean_box(v___y_503_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v___x_506_);
v___x_508_ = v___x_486_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_fst_483_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v___x_506_);
v___x_508_ = v_reuseFailAlloc_515_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_510_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_508_);
lean_ctor_set(v___x_481_, 0, v___x_505_);
v___x_510_ = v___x_481_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_510_);
v___x_512_ = v___x_500_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
lean_del_object(v___x_486_);
lean_dec(v_snd_484_);
lean_dec(v_fst_483_);
lean_del_object(v___x_481_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v_a_460_);
lean_dec_ref(v_d_459_);
v_a_547_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_497_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_497_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
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
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_del_object(v___x_486_);
lean_dec(v_snd_484_);
lean_dec(v_fst_483_);
lean_del_object(v___x_481_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v_a_460_);
lean_dec_ref(v_d_459_);
v_a_555_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_494_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_494_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_object* v___x_563_; 
lean_inc_ref(v___x_489_);
v___x_563_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_489_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref(v___x_563_);
v___x_565_ = lean_array_fset(v_fst_483_, v_a_460_, v_a_564_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_565_);
v___x_567_ = v___x_486_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_snd_484_);
v___x_567_ = v_reuseFailAlloc_571_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_567_);
lean_ctor_set(v___x_481_, 0, v___x_488_);
v___x_569_ = v___x_481_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
v_a_473_ = v___x_569_;
goto v___jp_472_;
}
}
}
else
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_579_; 
lean_del_object(v___x_486_);
lean_dec(v_snd_484_);
lean_dec(v_fst_483_);
lean_del_object(v___x_481_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v_a_460_);
lean_dec_ref(v_d_459_);
v_a_572_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_579_ == 0)
{
v___x_574_ = v___x_563_;
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_563_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_579_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v___x_577_; 
if (v_isShared_575_ == 0)
{
v___x_577_ = v___x_574_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_a_572_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_del_object(v___x_486_);
lean_dec(v_snd_484_);
lean_dec(v_fst_483_);
lean_del_object(v___x_481_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v_a_460_);
lean_dec_ref(v_d_459_);
v_a_580_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_491_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_491_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
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
else
{
uint8_t v___x_588_; 
v___x_588_ = l_Lean_Expr_hasMVar(v___x_489_);
if (v___x_588_ == 0)
{
lean_object* v___x_590_; 
if (v_isShared_487_ == 0)
{
v___x_590_ = v___x_486_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_fst_483_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_snd_484_);
v___x_590_ = v_reuseFailAlloc_594_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_592_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_590_);
lean_ctor_set(v___x_481_, 0, v___x_488_);
v___x_592_ = v___x_481_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
v_a_473_ = v___x_592_;
goto v___jp_472_;
}
}
}
else
{
lean_object* v___x_595_; 
lean_inc(v___x_489_);
v___x_595_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_489_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref(v___x_595_);
v___x_597_ = lean_array_fset(v_fst_483_, v_a_460_, v_a_596_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 0, v___x_597_);
v___x_599_ = v___x_486_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_snd_484_);
v___x_599_ = v_reuseFailAlloc_603_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_601_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_599_);
lean_ctor_set(v___x_481_, 0, v___x_488_);
v___x_601_ = v___x_481_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_602_, 1, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
v_a_473_ = v___x_601_;
goto v___jp_472_;
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_del_object(v___x_486_);
lean_dec(v_snd_484_);
lean_dec(v_fst_483_);
lean_del_object(v___x_481_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec(v_a_460_);
lean_dec_ref(v_d_459_);
v_a_604_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_595_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_595_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
}
}
v___jp_472_:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_add(v_a_460_, v___x_474_);
lean_dec(v_a_460_);
v_a_460_ = v___x_475_;
v_b_461_ = v_a_473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg___boxed(lean_object* v_upperBound_615_, lean_object* v_d_616_, lean_object* v_a_617_, lean_object* v_b_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_upperBound_615_, v_d_616_, v_a_617_, v_b_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
lean_dec(v_upperBound_615_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object* v_pattern_632_, lean_object* v_e_633_, uint8_t v___x_634_, lean_object* v_d_635_, lean_object* v_expr_636_, lean_object* v_rhs_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; 
lean_inc(v___y_646_);
lean_inc_ref(v___y_645_);
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
lean_inc(v___y_642_);
lean_inc_ref(v___y_641_);
lean_inc_ref(v_e_633_);
lean_inc_ref(v_pattern_632_);
v___x_648_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_632_, v_e_633_, v___x_634_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v_a_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_744_; 
v_a_649_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_744_ == 0)
{
v___x_651_ = v___x_648_;
v_isShared_652_ = v_isSharedCheck_744_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_a_649_);
lean_dec(v___x_648_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_744_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
if (lean_obj_tag(v_a_649_) == 1)
{
lean_object* v_val_653_; lean_object* v_us_654_; lean_object* v_args_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_739_; 
lean_del_object(v___x_651_);
v_val_653_ = lean_ctor_get(v_a_649_, 0);
lean_inc(v_val_653_);
lean_dec_ref(v_a_649_);
v_us_654_ = lean_ctor_get(v_val_653_, 0);
v_args_655_ = lean_ctor_get(v_val_653_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_val_653_);
if (v_isSharedCheck_739_ == 0)
{
v___x_657_ = v_val_653_;
v_isShared_658_ = v_isSharedCheck_739_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_args_655_);
lean_inc(v_us_654_);
lean_dec(v_val_653_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_739_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = lean_box(0);
v___x_660_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_us_654_, v___x_659_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref(v___x_660_);
v___x_662_ = lean_array_get_size(v_args_655_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = 0;
v___x_665_ = lean_box(0);
v___x_666_ = lean_box(v___x_664_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 1, v___x_666_);
lean_ctor_set(v___x_657_, 0, v_args_655_);
v___x_668_ = v___x_657_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_args_655_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_730_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_665_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
lean_inc(v___y_642_);
v___x_670_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v___x_662_, v_d_635_, v___x_663_, v___x_669_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_721_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_721_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_721_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_721_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v_fst_675_; 
v_fst_675_ = lean_ctor_get(v_a_671_, 0);
if (lean_obj_tag(v_fst_675_) == 0)
{
lean_object* v_snd_676_; lean_object* v_fst_677_; lean_object* v_snd_678_; lean_object* v_levelParams_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_del_object(v___x_673_);
v_snd_676_ = lean_ctor_get(v_a_671_, 1);
lean_inc(v_snd_676_);
lean_dec(v_a_671_);
v_fst_677_ = lean_ctor_get(v_snd_676_, 0);
lean_inc(v_fst_677_);
v_snd_678_ = lean_ctor_get(v_snd_676_, 1);
lean_inc(v_snd_678_);
lean_dec(v_snd_676_);
v_levelParams_679_ = lean_ctor_get(v_pattern_632_, 0);
lean_inc(v_levelParams_679_);
lean_inc(v_a_661_);
v___x_680_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(v_expr_636_, v_pattern_632_, v_a_661_, v_fst_677_);
v___x_681_ = l_Lean_Expr_instantiateLevelParams(v_rhs_637_, v_levelParams_679_, v_a_661_);
v___x_682_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_681_, v___y_642_);
if (lean_obj_tag(v___x_682_) == 0)
{
lean_object* v_a_683_; lean_object* v___x_684_; 
v_a_683_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_a_683_);
lean_dec_ref(v___x_682_);
v___x_684_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_a_683_, v_fst_677_, v___y_642_);
lean_dec(v___y_642_);
lean_dec(v_fst_677_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_700_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_700_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_700_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_700_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
uint8_t v___x_689_; 
v___x_689_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_633_, v_a_685_);
lean_dec_ref(v_e_633_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; uint8_t v___x_691_; lean_object* v___x_693_; 
v___x_690_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_690_, 0, v_a_685_);
lean_ctor_set(v___x_690_, 1, v___x_680_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*2, v___x_664_);
v___x_691_ = lean_unbox(v_snd_678_);
lean_dec(v_snd_678_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*2 + 1, v___x_691_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_690_);
v___x_693_ = v___x_687_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_690_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
else
{
uint8_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
lean_dec(v_a_685_);
lean_dec_ref(v___x_680_);
v___x_695_ = lean_unbox(v_snd_678_);
lean_dec(v_snd_678_);
v___x_696_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_695_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_696_);
v___x_698_ = v___x_687_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v___x_680_);
lean_dec(v_snd_678_);
lean_dec_ref(v_e_633_);
v_a_701_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_684_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_684_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v___x_680_);
lean_dec(v_snd_678_);
lean_dec(v_fst_677_);
lean_dec(v___y_642_);
lean_dec_ref(v_e_633_);
v_a_709_ = lean_ctor_get(v___x_682_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_682_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_682_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_682_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_object* v_val_717_; lean_object* v___x_719_; 
lean_inc_ref(v_fst_675_);
lean_dec(v_a_671_);
lean_dec(v_a_661_);
lean_dec(v___y_642_);
lean_dec_ref(v_expr_636_);
lean_dec_ref(v_e_633_);
lean_dec_ref(v_pattern_632_);
v_val_717_ = lean_ctor_get(v_fst_675_, 0);
lean_inc(v_val_717_);
lean_dec_ref(v_fst_675_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v_val_717_);
v___x_719_ = v___x_673_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_val_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_729_; 
lean_dec(v_a_661_);
lean_dec(v___y_642_);
lean_dec_ref(v_expr_636_);
lean_dec_ref(v_e_633_);
lean_dec_ref(v_pattern_632_);
v_a_722_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_729_ == 0)
{
v___x_724_ = v___x_670_;
v_isShared_725_ = v_isSharedCheck_729_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_670_);
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
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_del_object(v___x_657_);
lean_dec_ref(v_args_655_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v_expr_636_);
lean_dec_ref(v_d_635_);
lean_dec_ref(v_e_633_);
lean_dec_ref(v_pattern_632_);
v_a_731_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_660_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_660_);
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
else
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_dec(v_a_649_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v_expr_636_);
lean_dec_ref(v_d_635_);
lean_dec_ref(v_e_633_);
lean_dec_ref(v_pattern_632_);
v___x_740_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0));
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_740_);
v___x_742_ = v___x_651_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v_expr_636_);
lean_dec_ref(v_d_635_);
lean_dec_ref(v_e_633_);
lean_dec_ref(v_pattern_632_);
v_a_745_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_648_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_648_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object* v_pattern_753_, lean_object* v_e_754_, lean_object* v___x_755_, lean_object* v_d_756_, lean_object* v_expr_757_, lean_object* v_rhs_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
uint8_t v___x_32228__boxed_769_; lean_object* v_res_770_; 
v___x_32228__boxed_769_ = lean_unbox(v___x_755_);
v_res_770_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(v_pattern_753_, v_e_754_, v___x_32228__boxed_769_, v_d_756_, v_expr_757_, v_rhs_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_);
lean_dec_ref(v_rhs_758_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object* v_thm_771_, lean_object* v_e_772_, lean_object* v_d_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_expr_784_; lean_object* v_pattern_785_; lean_object* v_rhs_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___f_789_; uint8_t v___x_790_; lean_object* v___x_791_; 
v_expr_784_ = lean_ctor_get(v_thm_771_, 0);
lean_inc_ref(v_expr_784_);
v_pattern_785_ = lean_ctor_get(v_thm_771_, 1);
lean_inc_ref(v_pattern_785_);
v_rhs_786_ = lean_ctor_get(v_thm_771_, 2);
lean_inc_ref(v_rhs_786_);
lean_dec_ref(v_thm_771_);
v___x_787_ = 1;
v___x_788_ = lean_box(v___x_787_);
v___f_789_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed), 16, 6);
lean_closure_set(v___f_789_, 0, v_pattern_785_);
lean_closure_set(v___f_789_, 1, v_e_772_);
lean_closure_set(v___f_789_, 2, v___x_788_);
lean_closure_set(v___f_789_, 3, v_d_773_);
lean_closure_set(v___f_789_, 4, v_expr_784_);
lean_closure_set(v___f_789_, 5, v_rhs_786_);
v___x_790_ = 0;
v___x_791_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v___f_789_, v___x_790_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object* v_thm_792_, lean_object* v_e_793_, lean_object* v_d_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_thm_792_, v_e_793_, v_d_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(lean_object* v_mvarId_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_806_, v___y_813_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(lean_object* v_mvarId_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(v_mvarId_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec(v_mvarId_818_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(lean_object* v_mvarId_830_, lean_object* v_val_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_830_, v_val_831_, v___y_838_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(lean_object* v_mvarId_843_, lean_object* v_val_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(v_mvarId_843_, v_val_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(lean_object* v_upperBound_856_, lean_object* v_d_857_, lean_object* v___x_858_, lean_object* v_inst_859_, lean_object* v_R_860_, lean_object* v_a_861_, lean_object* v_b_862_, lean_object* v_c_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_upperBound_856_, v_d_857_, v_a_861_, v_b_862_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_875_ = _args[0];
lean_object* v_d_876_ = _args[1];
lean_object* v___x_877_ = _args[2];
lean_object* v_inst_878_ = _args[3];
lean_object* v_R_879_ = _args[4];
lean_object* v_a_880_ = _args[5];
lean_object* v_b_881_ = _args[6];
lean_object* v_c_882_ = _args[7];
lean_object* v___y_883_ = _args[8];
lean_object* v___y_884_ = _args[9];
lean_object* v___y_885_ = _args[10];
lean_object* v___y_886_ = _args[11];
lean_object* v___y_887_ = _args[12];
lean_object* v___y_888_ = _args[13];
lean_object* v___y_889_ = _args[14];
lean_object* v___y_890_ = _args[15];
lean_object* v___y_891_ = _args[16];
lean_object* v___y_892_ = _args[17];
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(v_upperBound_875_, v_d_876_, v___x_877_, v_inst_878_, v_R_879_, v_a_880_, v_b_881_, v_c_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___x_877_);
lean_dec(v_upperBound_875_);
return v_res_893_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_object* v_00_u03b2_894_, lean_object* v_x_895_, lean_object* v_x_896_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_895_, v_x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(lean_object* v_00_u03b2_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(v_00_u03b2_898_, v_x_899_, v_x_900_);
lean_dec(v_x_900_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(lean_object* v_00_u03b2_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_x_904_, v_x_905_, v_x_906_);
return v___x_907_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_908_, lean_object* v_x_909_, size_t v_x_910_, lean_object* v_x_911_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_909_, v_x_910_, v_x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_913_, lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
size_t v_x_32621__boxed_917_; uint8_t v_res_918_; lean_object* v_r_919_; 
v_x_32621__boxed_917_ = lean_unbox_usize(v_x_915_);
lean_dec(v_x_915_);
v_res_918_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(v_00_u03b2_913_, v_x_914_, v_x_32621__boxed_917_, v_x_916_);
lean_dec(v_x_916_);
v_r_919_ = lean_box(v_res_918_);
return v_r_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_920_, lean_object* v_x_921_, size_t v_x_922_, size_t v_x_923_, lean_object* v_x_924_, lean_object* v_x_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_921_, v_x_922_, v_x_923_, v_x_924_, v_x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_){
_start:
{
size_t v_x_32632__boxed_933_; size_t v_x_32633__boxed_934_; lean_object* v_res_935_; 
v_x_32632__boxed_933_ = lean_unbox_usize(v_x_929_);
lean_dec(v_x_929_);
v_x_32633__boxed_934_ = lean_unbox_usize(v_x_930_);
lean_dec(v_x_930_);
v_res_935_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(v_00_u03b2_927_, v_x_928_, v_x_32632__boxed_933_, v_x_32633__boxed_934_, v_x_931_, v_x_932_);
return v_res_935_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_936_, lean_object* v_keys_937_, lean_object* v_vals_938_, lean_object* v_heq_939_, lean_object* v_i_940_, lean_object* v_k_941_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_keys_937_, v_i_940_, v_k_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_943_, lean_object* v_keys_944_, lean_object* v_vals_945_, lean_object* v_heq_946_, lean_object* v_i_947_, lean_object* v_k_948_){
_start:
{
uint8_t v_res_949_; lean_object* v_r_950_; 
v_res_949_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(v_00_u03b2_943_, v_keys_944_, v_vals_945_, v_heq_946_, v_i_947_, v_k_948_);
lean_dec(v_k_948_);
lean_dec_ref(v_vals_945_);
lean_dec_ref(v_keys_944_);
v_r_950_ = lean_box(v_res_949_);
return v_r_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_951_, lean_object* v_n_952_, lean_object* v_k_953_, lean_object* v_v_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(v_n_952_, v_k_953_, v_v_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_956_, size_t v_depth_957_, lean_object* v_keys_958_, lean_object* v_vals_959_, lean_object* v_heq_960_, lean_object* v_i_961_, lean_object* v_entries_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_depth_957_, v_keys_958_, v_vals_959_, v_i_961_, v_entries_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_964_, lean_object* v_depth_965_, lean_object* v_keys_966_, lean_object* v_vals_967_, lean_object* v_heq_968_, lean_object* v_i_969_, lean_object* v_entries_970_){
_start:
{
size_t v_depth_boxed_971_; lean_object* v_res_972_; 
v_depth_boxed_971_ = lean_unbox_usize(v_depth_965_);
lean_dec(v_depth_965_);
v_res_972_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_964_, v_depth_boxed_971_, v_keys_966_, v_vals_967_, v_heq_968_, v_i_969_, v_entries_970_);
lean_dec_ref(v_vals_967_);
lean_dec_ref(v_keys_966_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_973_, lean_object* v_x_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(v_x_974_, v_x_975_, v_x_976_, v_x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(lean_object* v_fst_979_, lean_object* v_d_980_, lean_object* v_x_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_979_, v_x_981_, v_d_980_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed(lean_object* v_fst_993_, lean_object* v_d_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(v_fst_993_, v_d_994_, v_x_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object* v_d_1007_, lean_object* v_e_1008_, lean_object* v_as_1009_, size_t v_sz_1010_, size_t v_i_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
uint8_t v___y_1024_; lean_object* v___y_1025_; uint8_t v___y_1031_; lean_object* v___y_1032_; uint8_t v___y_1033_; uint8_t v___y_1036_; uint8_t v___y_1037_; lean_object* v___y_1038_; uint8_t v___y_1039_; uint8_t v___y_1041_; lean_object* v___y_1042_; uint8_t v___y_1043_; lean_object* v___y_1047_; uint8_t v___y_1048_; uint8_t v___x_1050_; 
v___x_1050_ = lean_usize_dec_lt(v_i_1011_, v_sz_1010_);
if (v___x_1050_ == 0)
{
lean_object* v___x_1051_; 
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v_e_1008_);
lean_dec_ref(v_d_1007_);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v_b_1012_);
return v___x_1051_;
}
else
{
lean_object* v_a_1052_; lean_object* v_fst_1053_; lean_object* v_snd_1054_; lean_object* v_snd_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1104_; 
v_a_1052_ = lean_array_uget_borrowed(v_as_1009_, v_i_1011_);
v_fst_1053_ = lean_ctor_get(v_a_1052_, 0);
v_snd_1054_ = lean_ctor_get(v_a_1052_, 1);
v_snd_1055_ = lean_ctor_get(v_b_1012_, 1);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_b_1012_);
if (v_isSharedCheck_1104_ == 0)
{
lean_object* v_unused_1105_; 
v_unused_1105_ = lean_ctor_get(v_b_1012_, 0);
lean_dec(v_unused_1105_);
v___x_1057_ = v_b_1012_;
v_isShared_1058_ = v_isSharedCheck_1104_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_snd_1055_);
lean_dec(v_b_1012_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1104_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___y_1061_; uint8_t v_done_1062_; uint8_t v___y_1063_; lean_object* v_result_1073_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1059_ = lean_box(0);
v___x_1081_ = lean_unsigned_to_nat(0u);
v___x_1082_ = lean_nat_dec_eq(v_snd_1054_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_object* v___f_1083_; lean_object* v___x_1084_; 
lean_inc_ref(v_d_1007_);
lean_inc(v_fst_1053_);
v___f_1083_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1083_, 0, v_fst_1053_);
lean_closure_set(v___f_1083_, 1, v_d_1007_);
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc_ref(v_e_1008_);
v___x_1084_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_1008_, v_snd_1054_, v___f_1083_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref(v___x_1084_);
v_result_1073_ = v_a_1085_;
goto v___jp_1072_;
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_del_object(v___x_1057_);
lean_dec(v_snd_1055_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v_e_1008_);
lean_dec_ref(v_d_1007_);
v_a_1086_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1084_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1084_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
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
else
{
lean_object* v___x_1094_; 
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
lean_inc(v___y_1013_);
lean_inc_ref(v_d_1007_);
lean_inc_ref(v_e_1008_);
lean_inc(v_fst_1053_);
v___x_1094_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1053_, v_e_1008_, v_d_1007_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref(v___x_1094_);
v_result_1073_ = v_a_1095_;
goto v___jp_1072_;
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_del_object(v___x_1057_);
lean_dec(v_snd_1055_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v_e_1008_);
lean_dec_ref(v_d_1007_);
v_a_1096_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1094_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1094_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
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
v___jp_1060_:
{
if (v_done_1062_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1066_; 
lean_dec_ref(v___y_1061_);
v___x_1064_ = lean_box(v___y_1063_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 1, v___x_1064_);
lean_ctor_set(v___x_1057_, 0, v___x_1059_);
v___x_1066_ = v___x_1057_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___x_1064_);
v___x_1066_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
size_t v___x_1067_; size_t v___x_1068_; 
v___x_1067_ = ((size_t)1ULL);
v___x_1068_ = lean_usize_add(v_i_1011_, v___x_1067_);
v_i_1011_ = v___x_1068_;
v_b_1012_ = v___x_1066_;
goto _start;
}
}
else
{
uint8_t v___x_1071_; 
lean_del_object(v___x_1057_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v_e_1008_);
lean_dec_ref(v_d_1007_);
v___x_1071_ = 0;
v___y_1041_ = v___y_1063_;
v___y_1042_ = v___y_1061_;
v___y_1043_ = v___x_1071_;
goto v___jp_1040_;
}
}
v___jp_1072_:
{
uint8_t v___x_1074_; 
v___x_1074_ = lean_unbox(v_snd_1055_);
if (v___x_1074_ == 0)
{
lean_dec(v_snd_1055_);
if (lean_obj_tag(v_result_1073_) == 0)
{
uint8_t v_done_1075_; uint8_t v_contextDependent_1076_; 
v_done_1075_ = lean_ctor_get_uint8(v_result_1073_, 0);
v_contextDependent_1076_ = lean_ctor_get_uint8(v_result_1073_, 1);
v___y_1061_ = v_result_1073_;
v_done_1062_ = v_done_1075_;
v___y_1063_ = v_contextDependent_1076_;
goto v___jp_1060_;
}
else
{
uint8_t v_contextDependent_1077_; 
lean_del_object(v___x_1057_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v_e_1008_);
lean_dec_ref(v_d_1007_);
v_contextDependent_1077_ = lean_ctor_get_uint8(v_result_1073_, sizeof(void*)*2 + 1);
v___y_1047_ = v_result_1073_;
v___y_1048_ = v_contextDependent_1077_;
goto v___jp_1046_;
}
}
else
{
if (lean_obj_tag(v_result_1073_) == 0)
{
uint8_t v_done_1078_; uint8_t v___x_1079_; 
v_done_1078_ = lean_ctor_get_uint8(v_result_1073_, 0);
v___x_1079_ = lean_unbox(v_snd_1055_);
lean_dec(v_snd_1055_);
v___y_1061_ = v_result_1073_;
v_done_1062_ = v_done_1078_;
v___y_1063_ = v___x_1079_;
goto v___jp_1060_;
}
else
{
uint8_t v___x_1080_; 
lean_del_object(v___x_1057_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v_e_1008_);
lean_dec_ref(v_d_1007_);
v___x_1080_ = lean_unbox(v_snd_1055_);
lean_dec(v_snd_1055_);
v___y_1047_ = v_result_1073_;
v___y_1048_ = v___x_1080_;
goto v___jp_1046_;
}
}
}
}
}
v___jp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v___y_1025_);
v___x_1027_ = lean_box(v___y_1024_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
v___jp_1030_:
{
if (v___y_1033_ == 0)
{
v___y_1024_ = v___y_1031_;
v___y_1025_ = v___y_1032_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1032_);
v___y_1024_ = v___y_1031_;
v___y_1025_ = v___x_1034_;
goto v___jp_1023_;
}
}
v___jp_1035_:
{
if (v___y_1039_ == 0)
{
v___y_1031_ = v___y_1037_;
v___y_1032_ = v___y_1038_;
v___y_1033_ = v___y_1037_;
goto v___jp_1030_;
}
else
{
v___y_1031_ = v___y_1037_;
v___y_1032_ = v___y_1038_;
v___y_1033_ = v___y_1036_;
goto v___jp_1030_;
}
}
v___jp_1040_:
{
if (v___y_1041_ == 0)
{
v___y_1024_ = v___y_1041_;
v___y_1025_ = v___y_1042_;
goto v___jp_1023_;
}
else
{
if (lean_obj_tag(v___y_1042_) == 0)
{
uint8_t v_contextDependent_1044_; 
v_contextDependent_1044_ = lean_ctor_get_uint8(v___y_1042_, 1);
v___y_1036_ = v___y_1043_;
v___y_1037_ = v___y_1041_;
v___y_1038_ = v___y_1042_;
v___y_1039_ = v_contextDependent_1044_;
goto v___jp_1035_;
}
else
{
uint8_t v_contextDependent_1045_; 
v_contextDependent_1045_ = lean_ctor_get_uint8(v___y_1042_, sizeof(void*)*2 + 1);
v___y_1036_ = v___y_1043_;
v___y_1037_ = v___y_1041_;
v___y_1038_ = v___y_1042_;
v___y_1039_ = v_contextDependent_1045_;
goto v___jp_1035_;
}
}
}
v___jp_1046_:
{
uint8_t v___x_1049_; 
v___x_1049_ = 0;
v___y_1041_ = v___y_1048_;
v___y_1042_ = v___y_1047_;
v___y_1043_ = v___x_1049_;
goto v___jp_1040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object* v_d_1106_, lean_object* v_e_1107_, lean_object* v_as_1108_, lean_object* v_sz_1109_, lean_object* v_i_1110_, lean_object* v_b_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
size_t v_sz_boxed_1122_; size_t v_i_boxed_1123_; lean_object* v_res_1124_; 
v_sz_boxed_1122_ = lean_unbox_usize(v_sz_1109_);
lean_dec(v_sz_1109_);
v_i_boxed_1123_ = lean_unbox_usize(v_i_1110_);
lean_dec(v_i_1110_);
v_res_1124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1106_, v_e_1107_, v_as_1108_, v_sz_boxed_1122_, v_i_boxed_1123_, v_b_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec_ref(v_as_1108_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object* v_thms_1129_, lean_object* v_d_1130_, lean_object* v_e_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; size_t v_sz_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
v___x_1142_ = l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(v_thms_1129_, v_e_1131_);
v___x_1143_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0));
v_sz_1144_ = lean_array_size(v___x_1142_);
v___x_1145_ = ((size_t)0ULL);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1130_, v_e_1131_, v___x_1142_, v_sz_1144_, v___x_1145_, v___x_1143_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec_ref(v___x_1142_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1162_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1162_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1162_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v_fst_1151_; 
v_fst_1151_ = lean_ctor_get(v_a_1147_, 0);
if (lean_obj_tag(v_fst_1151_) == 0)
{
lean_object* v_snd_1152_; uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v_snd_1152_ = lean_ctor_get(v_a_1147_, 1);
lean_inc(v_snd_1152_);
lean_dec(v_a_1147_);
v___x_1153_ = lean_unbox(v_snd_1152_);
lean_dec(v_snd_1152_);
v___x_1154_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1153_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1154_);
v___x_1156_ = v___x_1149_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
else
{
lean_object* v_val_1158_; lean_object* v___x_1160_; 
lean_inc_ref(v_fst_1151_);
lean_dec(v_a_1147_);
v_val_1158_ = lean_ctor_get(v_fst_1151_, 0);
lean_inc(v_val_1158_);
lean_dec_ref(v_fst_1151_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v_val_1158_);
v___x_1160_ = v___x_1149_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_val_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_a_1163_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1146_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1146_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object* v_thms_1171_, lean_object* v_d_1172_, lean_object* v_e_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_thms_1171_, v_d_1172_, v_e_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
return v_res_1184_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
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
