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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
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
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t v_x_30430__boxed_344_; size_t v_x_30431__boxed_345_; lean_object* v_res_346_; 
v_x_30430__boxed_344_ = lean_unbox_usize(v_x_340_);
lean_dec(v_x_340_);
v_x_30431__boxed_345_ = lean_unbox_usize(v_x_341_);
lean_dec(v_x_341_);
v_res_346_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_339_, v_x_30430__boxed_344_, v_x_30431__boxed_345_, v_x_342_, v_x_343_);
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
size_t v_x_30668__boxed_433_; uint8_t v_res_434_; lean_object* v_r_435_; 
v_x_30668__boxed_433_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_res_434_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_430_, v_x_30668__boxed_433_, v_x_432_);
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
lean_object* v_snd_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_587_; 
v_snd_479_ = lean_ctor_get(v_b_461_, 1);
v_isSharedCheck_587_ = !lean_is_exclusive(v_b_461_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v_b_461_, 0);
lean_dec(v_unused_588_);
v___x_481_ = v_b_461_;
v_isShared_482_ = v_isSharedCheck_587_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_snd_479_);
lean_dec(v_b_461_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_587_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_box(0);
v___x_484_ = lean_array_fget_borrowed(v_snd_479_, v_a_460_);
if (lean_obj_tag(v___x_484_) == 2)
{
lean_object* v_mvarId_485_; lean_object* v___x_486_; 
v_mvarId_485_ = lean_ctor_get(v___x_484_, 0);
v___x_486_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_485_, v___y_468_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; uint8_t v___x_488_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_a_487_);
lean_dec_ref(v___x_486_);
v___x_488_ = lean_unbox(v_a_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_inc(v_mvarId_485_);
v___x_489_ = l_Lean_MVarId_getDecl(v_mvarId_485_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v_type_491_; lean_object* v___x_492_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref(v___x_489_);
v_type_491_ = lean_ctor_get(v_a_490_, 2);
lean_inc_ref(v_type_491_);
lean_dec(v_a_490_);
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
v___x_492_ = lean_apply_11(v_d_459_, v_type_491_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, lean_box(0));
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_530_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_530_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_530_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_530_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
if (lean_obj_tag(v_a_493_) == 1)
{
lean_object* v_val_497_; lean_object* v___x_498_; 
lean_del_object(v___x_495_);
lean_dec(v_a_487_);
v_val_497_ = lean_ctor_get(v_a_493_, 0);
lean_inc(v_val_497_);
lean_dec_ref(v_a_493_);
v___x_498_ = l_Lean_Meta_Sym_instantiateMVarsS(v_val_497_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_500_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
lean_inc(v_a_499_);
lean_inc(v_mvarId_485_);
v___x_500_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_485_, v_a_499_, v___y_468_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v___x_501_; lean_object* v___x_503_; 
lean_dec_ref(v___x_500_);
v___x_501_ = lean_array_fset(v_snd_479_, v_a_460_, v_a_499_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_501_);
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_503_ = v___x_481_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
v_a_473_ = v___x_503_;
goto v___jp_472_;
}
}
else
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
lean_dec(v_a_499_);
lean_del_object(v___x_481_);
lean_dec(v_snd_479_);
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
v_a_505_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_512_ == 0)
{
v___x_507_ = v___x_500_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_500_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_a_505_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_del_object(v___x_481_);
lean_dec(v_snd_479_);
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
v_a_513_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_498_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_498_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
else
{
lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_525_; 
lean_dec(v_a_493_);
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
v___x_521_ = lean_alloc_ctor(0, 0, 1);
v___x_522_ = lean_unbox(v_a_487_);
lean_dec(v_a_487_);
lean_ctor_set_uint8(v___x_521_, 0, v___x_522_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_523_);
v___x_525_ = v___x_481_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_snd_479_);
v___x_525_ = v_reuseFailAlloc_529_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_527_; 
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_525_);
v___x_527_ = v___x_495_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_a_487_);
lean_del_object(v___x_481_);
lean_dec(v_snd_479_);
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
v_a_531_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_492_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_492_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_a_487_);
lean_del_object(v___x_481_);
lean_dec(v_snd_479_);
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
v_a_539_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_489_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_489_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
else
{
lean_object* v___x_547_; 
lean_dec(v_a_487_);
lean_inc_ref(v___x_484_);
v___x_547_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_484_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v_a_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc(v_a_548_);
lean_dec_ref(v___x_547_);
v___x_549_ = lean_array_fset(v_snd_479_, v_a_460_, v_a_548_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_549_);
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_551_ = v___x_481_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
v_a_473_ = v___x_551_;
goto v___jp_472_;
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_del_object(v___x_481_);
lean_dec(v_snd_479_);
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
v_a_553_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_547_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_547_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_del_object(v___x_481_);
lean_dec(v_snd_479_);
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
v_a_561_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_486_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_486_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
uint8_t v___x_569_; 
v___x_569_ = l_Lean_Expr_hasMVar(v___x_484_);
if (v___x_569_ == 0)
{
lean_object* v___x_571_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_571_ = v___x_481_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_snd_479_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
v_a_473_ = v___x_571_;
goto v___jp_472_;
}
}
else
{
lean_object* v___x_573_; 
lean_inc(v___x_484_);
v___x_573_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_484_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_573_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v_a_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc(v_a_574_);
lean_dec_ref(v___x_573_);
v___x_575_ = lean_array_fset(v_snd_479_, v_a_460_, v_a_574_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_575_);
lean_ctor_set(v___x_481_, 0, v___x_483_);
v___x_577_ = v___x_481_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
v_a_473_ = v___x_577_;
goto v___jp_472_;
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_del_object(v___x_481_);
lean_dec(v_snd_479_);
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
v_a_579_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_573_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_573_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg___boxed(lean_object* v_upperBound_589_, lean_object* v_d_590_, lean_object* v_a_591_, lean_object* v_b_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_upperBound_589_, v_d_590_, v_a_591_, v_b_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v_upperBound_589_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object* v_pattern_606_, lean_object* v_e_607_, uint8_t v___x_608_, lean_object* v_d_609_, lean_object* v_expr_610_, lean_object* v_rhs_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; 
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
lean_inc_ref(v_e_607_);
lean_inc_ref(v_pattern_606_);
v___x_622_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_606_, v_e_607_, v___x_608_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_711_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_711_ == 0)
{
v___x_625_ = v___x_622_;
v_isShared_626_ = v_isSharedCheck_711_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_622_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_711_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
if (lean_obj_tag(v_a_623_) == 1)
{
lean_object* v_val_627_; lean_object* v_us_628_; lean_object* v_args_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_706_; 
lean_del_object(v___x_625_);
v_val_627_ = lean_ctor_get(v_a_623_, 0);
lean_inc(v_val_627_);
lean_dec_ref(v_a_623_);
v_us_628_ = lean_ctor_get(v_val_627_, 0);
v_args_629_ = lean_ctor_get(v_val_627_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_val_627_);
if (v_isSharedCheck_706_ == 0)
{
v___x_631_ = v_val_627_;
v_isShared_632_ = v_isSharedCheck_706_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_args_629_);
lean_inc(v_us_628_);
lean_dec(v_val_627_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_706_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = lean_box(0);
v___x_634_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_us_628_, v___x_633_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref(v___x_634_);
v___x_636_ = lean_array_get_size(v_args_629_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = lean_box(0);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v___x_638_);
v___x_640_ = v___x_631_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_args_629_);
v___x_640_ = v_reuseFailAlloc_697_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; 
lean_inc(v___y_616_);
v___x_641_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v___x_636_, v_d_609_, v___x_637_, v___x_640_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_688_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_688_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_688_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_688_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v_fst_646_; 
v_fst_646_ = lean_ctor_get(v_a_642_, 0);
if (lean_obj_tag(v_fst_646_) == 0)
{
lean_object* v_snd_647_; lean_object* v_levelParams_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
lean_del_object(v___x_644_);
v_snd_647_ = lean_ctor_get(v_a_642_, 1);
lean_inc(v_snd_647_);
lean_dec(v_a_642_);
v_levelParams_648_ = lean_ctor_get(v_pattern_606_, 0);
lean_inc(v_levelParams_648_);
lean_inc(v_a_635_);
v___x_649_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(v_expr_610_, v_pattern_606_, v_a_635_, v_snd_647_);
v___x_650_ = l_Lean_Expr_instantiateLevelParams(v_rhs_611_, v_levelParams_648_, v_a_635_);
v___x_651_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_650_, v___y_616_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref(v___x_651_);
v___x_653_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_a_652_, v_snd_647_, v___y_616_);
lean_dec(v___y_616_);
lean_dec(v_snd_647_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_667_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_667_ == 0)
{
v___x_656_ = v___x_653_;
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
uint8_t v___x_658_; 
v___x_658_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_607_, v_a_654_);
lean_dec_ref(v_e_607_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_661_; 
v___x_659_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_659_, 0, v_a_654_);
lean_ctor_set(v___x_659_, 1, v___x_649_);
lean_ctor_set_uint8(v___x_659_, sizeof(void*)*2, v___x_658_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_659_);
v___x_661_ = v___x_656_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_665_; 
lean_dec(v_a_654_);
lean_dec_ref(v___x_649_);
v___x_663_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0));
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_663_);
v___x_665_ = v___x_656_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_663_);
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
else
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
lean_dec_ref(v___x_649_);
lean_dec_ref(v_e_607_);
v_a_668_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_675_ == 0)
{
v___x_670_ = v___x_653_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_653_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_a_668_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v___x_649_);
lean_dec(v_snd_647_);
lean_dec(v___y_616_);
lean_dec_ref(v_e_607_);
v_a_676_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_651_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_651_);
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
else
{
lean_object* v_val_684_; lean_object* v___x_686_; 
lean_inc_ref(v_fst_646_);
lean_dec(v_a_642_);
lean_dec(v_a_635_);
lean_dec(v___y_616_);
lean_dec_ref(v_expr_610_);
lean_dec_ref(v_e_607_);
lean_dec_ref(v_pattern_606_);
v_val_684_ = lean_ctor_get(v_fst_646_, 0);
lean_inc(v_val_684_);
lean_dec_ref(v_fst_646_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_val_684_);
v___x_686_ = v___x_644_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_val_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_dec(v_a_635_);
lean_dec(v___y_616_);
lean_dec_ref(v_expr_610_);
lean_dec_ref(v_e_607_);
lean_dec_ref(v_pattern_606_);
v_a_689_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_641_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_641_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_del_object(v___x_631_);
lean_dec_ref(v_args_629_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v_expr_610_);
lean_dec_ref(v_d_609_);
lean_dec_ref(v_e_607_);
lean_dec_ref(v_pattern_606_);
v_a_698_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_634_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_634_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_709_; 
lean_dec(v_a_623_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v_expr_610_);
lean_dec_ref(v_d_609_);
lean_dec_ref(v_e_607_);
lean_dec_ref(v_pattern_606_);
v___x_707_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0));
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_707_);
v___x_709_ = v___x_625_;
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
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v_expr_610_);
lean_dec_ref(v_d_609_);
lean_dec_ref(v_e_607_);
lean_dec_ref(v_pattern_606_);
v_a_712_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_622_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_622_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object* v_pattern_720_, lean_object* v_e_721_, lean_object* v___x_722_, lean_object* v_d_723_, lean_object* v_expr_724_, lean_object* v_rhs_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
uint8_t v___x_31006__boxed_736_; lean_object* v_res_737_; 
v___x_31006__boxed_736_ = lean_unbox(v___x_722_);
v_res_737_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(v_pattern_720_, v_e_721_, v___x_31006__boxed_736_, v_d_723_, v_expr_724_, v_rhs_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec_ref(v_rhs_725_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object* v_thm_738_, lean_object* v_e_739_, lean_object* v_d_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_expr_751_; lean_object* v_pattern_752_; lean_object* v_rhs_753_; uint8_t v___x_754_; lean_object* v___x_755_; lean_object* v___f_756_; uint8_t v___x_757_; lean_object* v___x_758_; 
v_expr_751_ = lean_ctor_get(v_thm_738_, 0);
lean_inc_ref(v_expr_751_);
v_pattern_752_ = lean_ctor_get(v_thm_738_, 1);
lean_inc_ref(v_pattern_752_);
v_rhs_753_ = lean_ctor_get(v_thm_738_, 2);
lean_inc_ref(v_rhs_753_);
lean_dec_ref(v_thm_738_);
v___x_754_ = 1;
v___x_755_ = lean_box(v___x_754_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed), 16, 6);
lean_closure_set(v___f_756_, 0, v_pattern_752_);
lean_closure_set(v___f_756_, 1, v_e_739_);
lean_closure_set(v___f_756_, 2, v___x_755_);
lean_closure_set(v___f_756_, 3, v_d_740_);
lean_closure_set(v___f_756_, 4, v_expr_751_);
lean_closure_set(v___f_756_, 5, v_rhs_753_);
v___x_757_ = 0;
v___x_758_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v___f_756_, v___x_757_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object* v_thm_759_, lean_object* v_e_760_, lean_object* v_d_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_thm_759_, v_e_760_, v_d_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(lean_object* v_mvarId_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_773_, v___y_780_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(lean_object* v_mvarId_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(v_mvarId_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec(v___y_786_);
lean_dec(v_mvarId_785_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(lean_object* v_mvarId_797_, lean_object* v_val_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_797_, v_val_798_, v___y_805_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(lean_object* v_mvarId_810_, lean_object* v_val_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(v_mvarId_810_, v_val_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(lean_object* v_upperBound_823_, lean_object* v_d_824_, lean_object* v___x_825_, lean_object* v_inst_826_, lean_object* v_R_827_, lean_object* v_a_828_, lean_object* v_b_829_, lean_object* v_c_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_upperBound_823_, v_d_824_, v_a_828_, v_b_829_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_842_ = _args[0];
lean_object* v_d_843_ = _args[1];
lean_object* v___x_844_ = _args[2];
lean_object* v_inst_845_ = _args[3];
lean_object* v_R_846_ = _args[4];
lean_object* v_a_847_ = _args[5];
lean_object* v_b_848_ = _args[6];
lean_object* v_c_849_ = _args[7];
lean_object* v___y_850_ = _args[8];
lean_object* v___y_851_ = _args[9];
lean_object* v___y_852_ = _args[10];
lean_object* v___y_853_ = _args[11];
lean_object* v___y_854_ = _args[12];
lean_object* v___y_855_ = _args[13];
lean_object* v___y_856_ = _args[14];
lean_object* v___y_857_ = _args[15];
lean_object* v___y_858_ = _args[16];
lean_object* v___y_859_ = _args[17];
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(v_upperBound_842_, v_d_843_, v___x_844_, v_inst_845_, v_R_846_, v_a_847_, v_b_848_, v_c_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___x_844_);
lean_dec(v_upperBound_842_);
return v_res_860_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_object* v_00_u03b2_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
uint8_t v___x_864_; 
v___x_864_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_862_, v_x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
uint8_t v_res_868_; lean_object* v_r_869_; 
v_res_868_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(v_00_u03b2_865_, v_x_866_, v_x_867_);
lean_dec(v_x_867_);
v_r_869_ = lean_box(v_res_868_);
return v_r_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(lean_object* v_00_u03b2_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_x_871_, v_x_872_, v_x_873_);
return v___x_874_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_875_, lean_object* v_x_876_, size_t v_x_877_, lean_object* v_x_878_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_876_, v_x_877_, v_x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
size_t v_x_31389__boxed_884_; uint8_t v_res_885_; lean_object* v_r_886_; 
v_x_31389__boxed_884_ = lean_unbox_usize(v_x_882_);
lean_dec(v_x_882_);
v_res_885_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(v_00_u03b2_880_, v_x_881_, v_x_31389__boxed_884_, v_x_883_);
lean_dec(v_x_883_);
v_r_886_ = lean_box(v_res_885_);
return v_r_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_887_, lean_object* v_x_888_, size_t v_x_889_, size_t v_x_890_, lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_888_, v_x_889_, v_x_890_, v_x_891_, v_x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_){
_start:
{
size_t v_x_31400__boxed_900_; size_t v_x_31401__boxed_901_; lean_object* v_res_902_; 
v_x_31400__boxed_900_ = lean_unbox_usize(v_x_896_);
lean_dec(v_x_896_);
v_x_31401__boxed_901_ = lean_unbox_usize(v_x_897_);
lean_dec(v_x_897_);
v_res_902_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(v_00_u03b2_894_, v_x_895_, v_x_31400__boxed_900_, v_x_31401__boxed_901_, v_x_898_, v_x_899_);
return v_res_902_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_903_, lean_object* v_keys_904_, lean_object* v_vals_905_, lean_object* v_heq_906_, lean_object* v_i_907_, lean_object* v_k_908_){
_start:
{
uint8_t v___x_909_; 
v___x_909_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_keys_904_, v_i_907_, v_k_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_910_, lean_object* v_keys_911_, lean_object* v_vals_912_, lean_object* v_heq_913_, lean_object* v_i_914_, lean_object* v_k_915_){
_start:
{
uint8_t v_res_916_; lean_object* v_r_917_; 
v_res_916_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(v_00_u03b2_910_, v_keys_911_, v_vals_912_, v_heq_913_, v_i_914_, v_k_915_);
lean_dec(v_k_915_);
lean_dec_ref(v_vals_912_);
lean_dec_ref(v_keys_911_);
v_r_917_ = lean_box(v_res_916_);
return v_r_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_918_, lean_object* v_n_919_, lean_object* v_k_920_, lean_object* v_v_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(v_n_919_, v_k_920_, v_v_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_923_, size_t v_depth_924_, lean_object* v_keys_925_, lean_object* v_vals_926_, lean_object* v_heq_927_, lean_object* v_i_928_, lean_object* v_entries_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_depth_924_, v_keys_925_, v_vals_926_, v_i_928_, v_entries_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_931_, lean_object* v_depth_932_, lean_object* v_keys_933_, lean_object* v_vals_934_, lean_object* v_heq_935_, lean_object* v_i_936_, lean_object* v_entries_937_){
_start:
{
size_t v_depth_boxed_938_; lean_object* v_res_939_; 
v_depth_boxed_938_ = lean_unbox_usize(v_depth_932_);
lean_dec(v_depth_932_);
v_res_939_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_931_, v_depth_boxed_938_, v_keys_933_, v_vals_934_, v_heq_935_, v_i_936_, v_entries_937_);
lean_dec_ref(v_vals_934_);
lean_dec_ref(v_keys_933_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_940_, lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_x_943_, lean_object* v_x_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(v_x_941_, v_x_942_, v_x_943_, v_x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(lean_object* v_fst_946_, lean_object* v_d_947_, lean_object* v_x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_946_, v_x_948_, v_d_947_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed(lean_object* v_fst_960_, lean_object* v_d_961_, lean_object* v_x_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(v_fst_960_, v_d_961_, v_x_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object* v_d_977_, lean_object* v_e_978_, lean_object* v_as_979_, size_t v_sz_980_, size_t v_i_981_, lean_object* v_b_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_lt(v_i_981_, v_sz_980_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v_e_978_);
lean_dec_ref(v_d_977_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v_b_982_);
return v___x_994_;
}
else
{
lean_object* v_a_995_; lean_object* v_fst_996_; lean_object* v_snd_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v_b_982_);
v_a_995_ = lean_array_uget(v_as_979_, v_i_981_);
v_fst_996_ = lean_ctor_get(v_a_995_, 0);
v_snd_997_ = lean_ctor_get(v_a_995_, 1);
v_isSharedCheck_1039_ = !lean_is_exclusive(v_a_995_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_999_ = v_a_995_;
v_isShared_1000_ = v_isSharedCheck_1039_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_snd_997_);
lean_inc(v_fst_996_);
lean_dec(v_a_995_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1039_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1001_; lean_object* v___y_1003_; lean_object* v___x_1009_; lean_object* v_result_1011_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1001_ = lean_box(0);
v___x_1009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___closed__0));
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_nat_dec_eq(v_snd_997_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___f_1018_; lean_object* v___x_1019_; 
lean_inc_ref(v_d_977_);
v___f_1018_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1018_, 0, v_fst_996_);
lean_closure_set(v___f_1018_, 1, v_d_977_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v_e_978_);
v___x_1019_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_978_, v_snd_997_, v___f_1018_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v_snd_997_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_a_1020_);
lean_dec_ref(v___x_1019_);
v_result_1011_ = v_a_1020_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1028_; 
lean_del_object(v___x_999_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v_e_978_);
lean_dec_ref(v_d_977_);
v_a_1021_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1028_ == 0)
{
v___x_1023_ = v___x_1019_;
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1019_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1028_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
lean_object* v___x_1026_; 
if (v_isShared_1024_ == 0)
{
v___x_1026_ = v___x_1023_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_a_1021_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v___x_1029_; 
lean_dec(v_snd_997_);
lean_inc(v___y_991_);
lean_inc_ref(v___y_990_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v_d_977_);
lean_inc_ref(v_e_978_);
v___x_1029_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_996_, v_e_978_, v_d_977_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
if (lean_obj_tag(v___x_1029_) == 0)
{
lean_object* v_a_1030_; 
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_a_1030_);
lean_dec_ref(v___x_1029_);
v_result_1011_ = v_a_1030_;
goto v___jp_1010_;
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_del_object(v___x_999_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v_e_978_);
lean_dec_ref(v_d_977_);
v_a_1031_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1029_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1029_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
v___jp_1002_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___y_1003_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 1, v___x_1001_);
lean_ctor_set(v___x_999_, 0, v___x_1004_);
v___x_1006_ = v___x_999_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v___x_1001_);
v___x_1006_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
}
v___jp_1010_:
{
if (lean_obj_tag(v_result_1011_) == 0)
{
uint8_t v_done_1012_; 
v_done_1012_ = lean_ctor_get_uint8(v_result_1011_, 0);
if (v_done_1012_ == 0)
{
size_t v___x_1013_; size_t v___x_1014_; 
lean_dec_ref(v_result_1011_);
lean_del_object(v___x_999_);
v___x_1013_ = ((size_t)1ULL);
v___x_1014_ = lean_usize_add(v_i_981_, v___x_1013_);
v_i_981_ = v___x_1014_;
v_b_982_ = v___x_1009_;
goto _start;
}
else
{
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v_e_978_);
lean_dec_ref(v_d_977_);
v___y_1003_ = v_result_1011_;
goto v___jp_1002_;
}
}
else
{
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v_e_978_);
lean_dec_ref(v_d_977_);
v___y_1003_ = v_result_1011_;
goto v___jp_1002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object* v_d_1040_, lean_object* v_e_1041_, lean_object* v_as_1042_, lean_object* v_sz_1043_, lean_object* v_i_1044_, lean_object* v_b_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
size_t v_sz_boxed_1056_; size_t v_i_boxed_1057_; lean_object* v_res_1058_; 
v_sz_boxed_1056_ = lean_unbox_usize(v_sz_1043_);
lean_dec(v_sz_1043_);
v_i_boxed_1057_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_res_1058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1040_, v_e_1041_, v_as_1042_, v_sz_boxed_1056_, v_i_boxed_1057_, v_b_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec_ref(v_as_1042_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object* v_thms_1059_, lean_object* v_d_1060_, lean_object* v_e_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; size_t v_sz_1074_; size_t v___x_1075_; lean_object* v___x_1076_; 
v___x_1072_ = l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(v_thms_1059_, v_e_1061_);
v___x_1073_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___closed__0));
v_sz_1074_ = lean_array_size(v___x_1072_);
v___x_1075_ = ((size_t)0ULL);
v___x_1076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1060_, v_e_1061_, v___x_1072_, v_sz_1074_, v___x_1075_, v___x_1073_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
lean_dec_ref(v___x_1072_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1090_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1079_ = v___x_1076_;
v_isShared_1080_ = v_isSharedCheck_1090_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1076_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1090_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v_fst_1081_; 
v_fst_1081_ = lean_ctor_get(v_a_1077_, 0);
lean_inc(v_fst_1081_);
lean_dec(v_a_1077_);
if (lean_obj_tag(v_fst_1081_) == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0));
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1082_);
v___x_1084_ = v___x_1079_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
else
{
lean_object* v_val_1086_; lean_object* v___x_1088_; 
v_val_1086_ = lean_ctor_get(v_fst_1081_, 0);
lean_inc(v_val_1086_);
lean_dec_ref(v_fst_1081_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v_val_1086_);
v___x_1088_ = v___x_1079_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_val_1086_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v_a_1091_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1076_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1076_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object* v_thms_1099_, lean_object* v_d_1100_, lean_object* v_e_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_thms_1099_, v_d_1100_, v_e_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
return v_res_1112_;
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
