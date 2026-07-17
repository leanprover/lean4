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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_match_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_expr_1_, 2);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0(void){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(lean_object* v_x_256_, size_t v_x_257_, size_t v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_256_) == 0)
{
lean_object* v_es_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v_j_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_es_261_ = lean_ctor_get(v_x_256_, 0);
v___x_262_ = ((size_t)31ULL);
v___x_263_ = lean_usize_land(v_x_257_, v___x_262_);
v_j_264_ = lean_usize_to_nat(v___x_263_);
v___x_265_ = lean_array_get_size(v_es_261_);
v___x_266_ = lean_nat_dec_lt(v_j_264_, v___x_265_);
if (v___x_266_ == 0)
{
lean_dec(v_j_264_);
lean_dec(v_x_260_);
lean_dec(v_x_259_);
return v_x_256_;
}
else
{
lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_305_; 
lean_inc_ref(v_es_261_);
v_isSharedCheck_305_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v_x_256_, 0);
lean_dec(v_unused_306_);
v___x_268_ = v_x_256_;
v_isShared_269_ = v_isSharedCheck_305_;
goto v_resetjp_267_;
}
else
{
lean_dec(v_x_256_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_305_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_v_270_; lean_object* v___x_271_; lean_object* v_xs_x27_272_; lean_object* v___y_274_; 
v_v_270_ = lean_array_fget(v_es_261_, v_j_264_);
v___x_271_ = lean_box(0);
v_xs_x27_272_ = lean_array_fset(v_es_261_, v_j_264_, v___x_271_);
switch(lean_obj_tag(v_v_270_))
{
case 0:
{
lean_object* v_key_279_; lean_object* v_val_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_290_; 
v_key_279_ = lean_ctor_get(v_v_270_, 0);
v_val_280_ = lean_ctor_get(v_v_270_, 1);
v_isSharedCheck_290_ = !lean_is_exclusive(v_v_270_);
if (v_isSharedCheck_290_ == 0)
{
v___x_282_ = v_v_270_;
v_isShared_283_ = v_isSharedCheck_290_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_val_280_);
lean_inc(v_key_279_);
lean_dec(v_v_270_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_290_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
uint8_t v___x_284_; 
v___x_284_ = l_Lean_instBEqMVarId_beq(v_x_259_, v_key_279_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; 
lean_del_object(v___x_282_);
v___x_285_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_279_, v_val_280_, v_x_259_, v_x_260_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
v___y_274_ = v___x_286_;
goto v___jp_273_;
}
else
{
lean_object* v___x_288_; 
lean_dec(v_val_280_);
lean_dec(v_key_279_);
if (v_isShared_283_ == 0)
{
lean_ctor_set(v___x_282_, 1, v_x_260_);
lean_ctor_set(v___x_282_, 0, v_x_259_);
v___x_288_ = v___x_282_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_x_259_);
lean_ctor_set(v_reuseFailAlloc_289_, 1, v_x_260_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
v___y_274_ = v___x_288_;
goto v___jp_273_;
}
}
}
}
case 1:
{
lean_object* v_node_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_303_; 
v_node_291_ = lean_ctor_get(v_v_270_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v_v_270_);
if (v_isSharedCheck_303_ == 0)
{
v___x_293_ = v_v_270_;
v_isShared_294_ = v_isSharedCheck_303_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_node_291_);
lean_dec(v_v_270_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_303_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_295_ = ((size_t)5ULL);
v___x_296_ = lean_usize_shift_right(v_x_257_, v___x_295_);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_add(v_x_258_, v___x_297_);
v___x_299_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_node_291_, v___x_296_, v___x_298_, v_x_259_, v_x_260_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_299_);
v___x_301_ = v___x_293_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
v___y_274_ = v___x_301_;
goto v___jp_273_;
}
}
}
default: 
{
lean_object* v___x_304_; 
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v_x_259_);
lean_ctor_set(v___x_304_, 1, v_x_260_);
v___y_274_ = v___x_304_;
goto v___jp_273_;
}
}
v___jp_273_:
{
lean_object* v___x_275_; lean_object* v___x_277_; 
v___x_275_ = lean_array_fset(v_xs_x27_272_, v_j_264_, v___y_274_);
lean_dec(v_j_264_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_275_);
v___x_277_ = v___x_268_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_275_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
else
{
lean_object* v_ks_307_; lean_object* v_vs_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_328_; 
v_ks_307_ = lean_ctor_get(v_x_256_, 0);
v_vs_308_ = lean_ctor_get(v_x_256_, 1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_256_);
if (v_isSharedCheck_328_ == 0)
{
v___x_310_ = v_x_256_;
v_isShared_311_ = v_isSharedCheck_328_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_vs_308_);
lean_inc(v_ks_307_);
lean_dec(v_x_256_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_328_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_ks_307_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_vs_308_);
v___x_313_ = v_reuseFailAlloc_327_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v_newNode_314_; uint8_t v___y_316_; size_t v___x_322_; uint8_t v___x_323_; 
v_newNode_314_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(v___x_313_, v_x_259_, v_x_260_);
v___x_322_ = ((size_t)7ULL);
v___x_323_ = lean_usize_dec_le(v___x_322_, v_x_258_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_324_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_314_);
v___x_325_ = lean_unsigned_to_nat(4u);
v___x_326_ = lean_nat_dec_lt(v___x_324_, v___x_325_);
lean_dec(v___x_324_);
v___y_316_ = v___x_326_;
goto v___jp_315_;
}
else
{
v___y_316_ = v___x_323_;
goto v___jp_315_;
}
v___jp_315_:
{
if (v___y_316_ == 0)
{
lean_object* v_ks_317_; lean_object* v_vs_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v_ks_317_ = lean_ctor_get(v_newNode_314_, 0);
lean_inc_ref(v_ks_317_);
v_vs_318_ = lean_ctor_get(v_newNode_314_, 1);
lean_inc_ref(v_vs_318_);
lean_dec_ref(v_newNode_314_);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___closed__0);
v___x_321_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_x_258_, v_ks_317_, v_vs_318_, v___x_319_, v___x_320_);
lean_dec_ref(v_vs_318_);
lean_dec_ref(v_ks_317_);
return v___x_321_;
}
else
{
return v_newNode_314_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(size_t v_depth_329_, lean_object* v_keys_330_, lean_object* v_vals_331_, lean_object* v_i_332_, lean_object* v_entries_333_){
_start:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_array_get_size(v_keys_330_);
v___x_335_ = lean_nat_dec_lt(v_i_332_, v___x_334_);
if (v___x_335_ == 0)
{
lean_dec(v_i_332_);
return v_entries_333_;
}
else
{
lean_object* v_k_336_; lean_object* v_v_337_; uint64_t v___x_338_; size_t v_h_339_; size_t v___x_340_; lean_object* v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; size_t v_h_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_k_336_ = lean_array_fget_borrowed(v_keys_330_, v_i_332_);
v_v_337_ = lean_array_fget_borrowed(v_vals_331_, v_i_332_);
v___x_338_ = l_Lean_instHashableMVarId_hash(v_k_336_);
v_h_339_ = lean_uint64_to_usize(v___x_338_);
v___x_340_ = ((size_t)5ULL);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_sub(v_depth_329_, v___x_342_);
v___x_344_ = lean_usize_mul(v___x_340_, v___x_343_);
v_h_345_ = lean_usize_shift_right(v_h_339_, v___x_344_);
v___x_346_ = lean_nat_add(v_i_332_, v___x_341_);
lean_dec(v_i_332_);
lean_inc(v_v_337_);
lean_inc(v_k_336_);
v___x_347_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_entries_333_, v_h_345_, v_depth_329_, v_k_336_, v_v_337_);
v_i_332_ = v___x_346_;
v_entries_333_ = v___x_347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_depth_349_, lean_object* v_keys_350_, lean_object* v_vals_351_, lean_object* v_i_352_, lean_object* v_entries_353_){
_start:
{
size_t v_depth_boxed_354_; lean_object* v_res_355_; 
v_depth_boxed_354_ = lean_unbox_usize(v_depth_349_);
lean_dec(v_depth_349_);
v_res_355_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_depth_boxed_354_, v_keys_350_, v_vals_351_, v_i_352_, v_entries_353_);
lean_dec_ref(v_vals_351_);
lean_dec_ref(v_keys_350_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_356_, lean_object* v_x_357_, lean_object* v_x_358_, lean_object* v_x_359_, lean_object* v_x_360_){
_start:
{
size_t v_x_40602__boxed_361_; size_t v_x_40603__boxed_362_; lean_object* v_res_363_; 
v_x_40602__boxed_361_ = lean_unbox_usize(v_x_357_);
lean_dec(v_x_357_);
v_x_40603__boxed_362_ = lean_unbox_usize(v_x_358_);
lean_dec(v_x_358_);
v_res_363_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_356_, v_x_40602__boxed_361_, v_x_40603__boxed_362_, v_x_359_, v_x_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_x_366_){
_start:
{
uint64_t v___x_367_; size_t v___x_368_; size_t v___x_369_; lean_object* v___x_370_; 
v___x_367_ = l_Lean_instHashableMVarId_hash(v_x_365_);
v___x_368_ = lean_uint64_to_usize(v___x_367_);
v___x_369_ = ((size_t)1ULL);
v___x_370_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_364_, v___x_368_, v___x_369_, v_x_365_, v_x_366_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(lean_object* v_mvarId_371_, lean_object* v_val_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; lean_object* v_mctx_376_; lean_object* v_cache_377_; lean_object* v_zetaDeltaFVarIds_378_; lean_object* v_postponed_379_; lean_object* v_diag_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_408_; 
v___x_375_ = lean_st_ref_take(v___y_373_);
v_mctx_376_ = lean_ctor_get(v___x_375_, 0);
v_cache_377_ = lean_ctor_get(v___x_375_, 1);
v_zetaDeltaFVarIds_378_ = lean_ctor_get(v___x_375_, 2);
v_postponed_379_ = lean_ctor_get(v___x_375_, 3);
v_diag_380_ = lean_ctor_get(v___x_375_, 4);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_408_ == 0)
{
v___x_382_ = v___x_375_;
v_isShared_383_ = v_isSharedCheck_408_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_diag_380_);
lean_inc(v_postponed_379_);
lean_inc(v_zetaDeltaFVarIds_378_);
lean_inc(v_cache_377_);
lean_inc(v_mctx_376_);
lean_dec(v___x_375_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_408_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v_depth_384_; lean_object* v_levelAssignDepth_385_; lean_object* v_lmvarCounter_386_; lean_object* v_mvarCounter_387_; lean_object* v_lDecls_388_; lean_object* v_decls_389_; lean_object* v_userNames_390_; lean_object* v_lAssignment_391_; lean_object* v_eAssignment_392_; lean_object* v_dAssignment_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_407_; 
v_depth_384_ = lean_ctor_get(v_mctx_376_, 0);
v_levelAssignDepth_385_ = lean_ctor_get(v_mctx_376_, 1);
v_lmvarCounter_386_ = lean_ctor_get(v_mctx_376_, 2);
v_mvarCounter_387_ = lean_ctor_get(v_mctx_376_, 3);
v_lDecls_388_ = lean_ctor_get(v_mctx_376_, 4);
v_decls_389_ = lean_ctor_get(v_mctx_376_, 5);
v_userNames_390_ = lean_ctor_get(v_mctx_376_, 6);
v_lAssignment_391_ = lean_ctor_get(v_mctx_376_, 7);
v_eAssignment_392_ = lean_ctor_get(v_mctx_376_, 8);
v_dAssignment_393_ = lean_ctor_get(v_mctx_376_, 9);
v_isSharedCheck_407_ = !lean_is_exclusive(v_mctx_376_);
if (v_isSharedCheck_407_ == 0)
{
v___x_395_ = v_mctx_376_;
v_isShared_396_ = v_isSharedCheck_407_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_dAssignment_393_);
lean_inc(v_eAssignment_392_);
lean_inc(v_lAssignment_391_);
lean_inc(v_userNames_390_);
lean_inc(v_decls_389_);
lean_inc(v_lDecls_388_);
lean_inc(v_mvarCounter_387_);
lean_inc(v_lmvarCounter_386_);
lean_inc(v_levelAssignDepth_385_);
lean_inc(v_depth_384_);
lean_dec(v_mctx_376_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_407_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_397_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_eAssignment_392_, v_mvarId_371_, v_val_372_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 8, v___x_397_);
v___x_399_ = v___x_395_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_depth_384_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_levelAssignDepth_385_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_lmvarCounter_386_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_mvarCounter_387_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_lDecls_388_);
lean_ctor_set(v_reuseFailAlloc_406_, 5, v_decls_389_);
lean_ctor_set(v_reuseFailAlloc_406_, 6, v_userNames_390_);
lean_ctor_set(v_reuseFailAlloc_406_, 7, v_lAssignment_391_);
lean_ctor_set(v_reuseFailAlloc_406_, 8, v___x_397_);
lean_ctor_set(v_reuseFailAlloc_406_, 9, v_dAssignment_393_);
v___x_399_ = v_reuseFailAlloc_406_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_401_; 
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 0, v___x_399_);
v___x_401_ = v___x_382_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_cache_377_);
lean_ctor_set(v_reuseFailAlloc_405_, 2, v_zetaDeltaFVarIds_378_);
lean_ctor_set(v_reuseFailAlloc_405_, 3, v_postponed_379_);
lean_ctor_set(v_reuseFailAlloc_405_, 4, v_diag_380_);
v___x_401_ = v_reuseFailAlloc_405_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_st_ref_set(v___y_373_, v___x_401_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
return v___x_404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(lean_object* v_mvarId_409_, lean_object* v_val_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_409_, v_val_410_, v___y_411_);
lean_dec(v___y_411_);
return v_res_413_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(lean_object* v_keys_414_, lean_object* v_i_415_, lean_object* v_k_416_){
_start:
{
lean_object* v___x_417_; uint8_t v___x_418_; 
v___x_417_ = lean_array_get_size(v_keys_414_);
v___x_418_ = lean_nat_dec_lt(v_i_415_, v___x_417_);
if (v___x_418_ == 0)
{
lean_dec(v_i_415_);
return v___x_418_;
}
else
{
lean_object* v_k_x27_419_; uint8_t v___x_420_; 
v_k_x27_419_ = lean_array_fget_borrowed(v_keys_414_, v_i_415_);
v___x_420_ = l_Lean_instBEqMVarId_beq(v_k_416_, v_k_x27_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_i_415_, v___x_421_);
lean_dec(v_i_415_);
v_i_415_ = v___x_422_;
goto _start;
}
else
{
lean_dec(v_i_415_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg___boxed(lean_object* v_keys_424_, lean_object* v_i_425_, lean_object* v_k_426_){
_start:
{
uint8_t v_res_427_; lean_object* v_r_428_; 
v_res_427_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_keys_424_, v_i_425_, v_k_426_);
lean_dec(v_k_426_);
lean_dec_ref(v_keys_424_);
v_r_428_ = lean_box(v_res_427_);
return v_r_428_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(lean_object* v_x_429_, size_t v_x_430_, lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_object* v_es_432_; lean_object* v___x_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v_j_436_; lean_object* v___x_437_; 
v_es_432_ = lean_ctor_get(v_x_429_, 0);
v___x_433_ = lean_box(2);
v___x_434_ = ((size_t)31ULL);
v___x_435_ = lean_usize_land(v_x_430_, v___x_434_);
v_j_436_ = lean_usize_to_nat(v___x_435_);
v___x_437_ = lean_array_get_borrowed(v___x_433_, v_es_432_, v_j_436_);
lean_dec(v_j_436_);
switch(lean_obj_tag(v___x_437_))
{
case 0:
{
lean_object* v_key_438_; uint8_t v___x_439_; 
v_key_438_ = lean_ctor_get(v___x_437_, 0);
v___x_439_ = l_Lean_instBEqMVarId_beq(v_x_431_, v_key_438_);
return v___x_439_;
}
case 1:
{
lean_object* v_node_440_; size_t v___x_441_; size_t v___x_442_; 
v_node_440_ = lean_ctor_get(v___x_437_, 0);
v___x_441_ = ((size_t)5ULL);
v___x_442_ = lean_usize_shift_right(v_x_430_, v___x_441_);
v_x_429_ = v_node_440_;
v_x_430_ = v___x_442_;
goto _start;
}
default: 
{
uint8_t v___x_444_; 
v___x_444_ = 0;
return v___x_444_;
}
}
}
else
{
lean_object* v_ks_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_ks_445_ = lean_ctor_get(v_x_429_, 0);
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_ks_445_, v___x_446_, v_x_431_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg___boxed(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
size_t v_x_40828__boxed_451_; uint8_t v_res_452_; lean_object* v_r_453_; 
v_x_40828__boxed_451_ = lean_unbox_usize(v_x_449_);
lean_dec(v_x_449_);
v_res_452_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_448_, v_x_40828__boxed_451_, v_x_450_);
lean_dec(v_x_450_);
lean_dec_ref(v_x_448_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
uint64_t v___x_456_; size_t v___x_457_; uint8_t v___x_458_; 
v___x_456_ = l_Lean_instHashableMVarId_hash(v_x_455_);
v___x_457_ = lean_uint64_to_usize(v___x_456_);
v___x_458_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_454_, v___x_457_, v_x_455_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg___boxed(lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_459_, v_x_460_);
lean_dec(v_x_460_);
lean_dec_ref(v_x_459_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(lean_object* v_mvarId_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___x_466_; lean_object* v_mctx_467_; lean_object* v_eAssignment_468_; uint8_t v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_466_ = lean_st_ref_get(v___y_464_);
v_mctx_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc_ref(v_mctx_467_);
lean_dec(v___x_466_);
v_eAssignment_468_ = lean_ctor_get(v_mctx_467_, 8);
lean_inc_ref(v_eAssignment_468_);
lean_dec_ref(v_mctx_467_);
v___x_469_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_eAssignment_468_, v_mvarId_463_);
lean_dec_ref(v_eAssignment_468_);
v___x_470_ = lean_box(v___x_469_);
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg___boxed(lean_object* v_mvarId_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec(v_mvarId_472_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(lean_object* v_upperBound_476_, lean_object* v_mvarCounterSaved_477_, lean_object* v_d_478_, lean_object* v_a_479_, lean_object* v_b_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_a_492_; uint8_t v___x_496_; 
v___x_496_ = lean_nat_dec_lt(v_a_479_, v_upperBound_476_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec(v_a_479_);
lean_dec_ref(v_d_478_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v_b_480_);
return v___x_497_;
}
else
{
lean_object* v_snd_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_640_; 
v_snd_498_ = lean_ctor_get(v_b_480_, 1);
v_isSharedCheck_640_ = !lean_is_exclusive(v_b_480_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v_b_480_, 0);
lean_dec(v_unused_641_);
v___x_500_ = v_b_480_;
v_isShared_501_ = v_isSharedCheck_640_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_snd_498_);
lean_dec(v_b_480_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_640_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v_fst_502_; lean_object* v_snd_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_639_; 
v_fst_502_ = lean_ctor_get(v_snd_498_, 0);
v_snd_503_ = lean_ctor_get(v_snd_498_, 1);
v_isSharedCheck_639_ = !lean_is_exclusive(v_snd_498_);
if (v_isSharedCheck_639_ == 0)
{
v___x_505_ = v_snd_498_;
v_isShared_506_ = v_isSharedCheck_639_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_snd_503_);
lean_inc(v_fst_502_);
lean_dec(v_snd_498_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_639_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_box(0);
v___x_508_ = lean_array_fget_borrowed(v_fst_502_, v_a_479_);
if (lean_obj_tag(v___x_508_) == 2)
{
lean_object* v_mvarId_509_; lean_object* v___x_510_; 
v_mvarId_509_ = lean_ctor_get(v___x_508_, 0);
v___x_510_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_509_, v___y_487_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; uint8_t v___x_512_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_510_, 1);
v___x_512_ = lean_unbox(v_a_511_);
lean_dec(v_a_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; 
lean_inc(v_mvarId_509_);
v___x_513_ = l_Lean_MVarId_getDecl(v_mvarId_509_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v_type_515_; lean_object* v_index_516_; uint8_t v___x_517_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v_type_515_ = lean_ctor_get(v_a_514_, 2);
lean_inc_ref(v_type_515_);
v_index_516_ = lean_ctor_get(v_a_514_, 6);
lean_inc(v_index_516_);
lean_dec(v_a_514_);
v___x_517_ = lean_nat_dec_le(v_mvarCounterSaved_477_, v_index_516_);
lean_dec(v_index_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_519_; 
lean_dec_ref(v_type_515_);
if (v_isShared_506_ == 0)
{
v___x_519_ = v___x_505_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_fst_502_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_snd_503_);
v___x_519_ = v_reuseFailAlloc_523_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_521_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_519_);
lean_ctor_set(v___x_500_, 0, v___x_507_);
v___x_521_ = v___x_500_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
v_a_492_ = v___x_521_;
goto v___jp_491_;
}
}
}
else
{
lean_object* v___x_524_; 
lean_inc_ref(v_d_478_);
lean_inc(v___y_489_);
lean_inc_ref(v___y_488_);
lean_inc(v___y_487_);
lean_inc_ref(v___y_486_);
lean_inc(v___y_485_);
lean_inc_ref(v___y_484_);
lean_inc(v___y_483_);
lean_inc_ref(v___y_482_);
lean_inc(v___y_481_);
v___x_524_ = lean_apply_11(v_d_478_, v_type_515_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, lean_box(0));
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_573_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_573_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_573_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_573_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
uint8_t v___y_530_; 
if (lean_obj_tag(v_a_525_) == 0)
{
uint8_t v___x_543_; 
lean_dec(v_a_479_);
lean_dec_ref(v_d_478_);
v___x_543_ = lean_unbox(v_snd_503_);
lean_dec(v_snd_503_);
if (v___x_543_ == 0)
{
uint8_t v_contextDependent_544_; 
v_contextDependent_544_ = lean_ctor_get_uint8(v_a_525_, 0);
lean_dec_ref_known(v_a_525_, 0);
v___y_530_ = v_contextDependent_544_;
goto v___jp_529_;
}
else
{
lean_dec_ref_known(v_a_525_, 0);
v___y_530_ = v___x_517_;
goto v___jp_529_;
}
}
else
{
lean_object* v_proof_545_; uint8_t v_contextDependent_546_; uint8_t v___y_548_; uint8_t v___x_572_; 
lean_del_object(v___x_527_);
lean_del_object(v___x_505_);
lean_del_object(v___x_500_);
v_proof_545_ = lean_ctor_get(v_a_525_, 0);
lean_inc_ref(v_proof_545_);
v_contextDependent_546_ = lean_ctor_get_uint8(v_a_525_, sizeof(void*)*1);
lean_dec_ref_known(v_a_525_, 1);
v___x_572_ = lean_unbox(v_snd_503_);
lean_dec(v_snd_503_);
if (v___x_572_ == 0)
{
v___y_548_ = v_contextDependent_546_;
goto v___jp_547_;
}
else
{
v___y_548_ = v___x_517_;
goto v___jp_547_;
}
v___jp_547_:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_Meta_Sym_instantiateMVarsS(v_proof_545_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_551_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc_n(v_a_550_, 2);
lean_dec_ref_known(v___x_549_, 1);
lean_inc(v_mvarId_509_);
v___x_551_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_509_, v_a_550_, v___y_487_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref_known(v___x_551_, 1);
v___x_552_ = lean_array_fset(v_fst_502_, v_a_479_, v_a_550_);
v___x_553_ = lean_box(v___y_548_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_507_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v_a_492_ = v___x_555_;
goto v___jp_491_;
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec(v_a_550_);
lean_dec(v_fst_502_);
lean_dec(v_a_479_);
lean_dec_ref(v_d_478_);
v_a_556_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_551_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_551_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec(v_fst_502_);
lean_dec(v_a_479_);
lean_dec_ref(v_d_478_);
v_a_564_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_549_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_549_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
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
v___jp_529_:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_531_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_530_);
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
v___x_533_ = lean_box(v___y_530_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v___x_533_);
v___x_535_ = v___x_505_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_fst_502_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v___x_533_);
v___x_535_ = v_reuseFailAlloc_542_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_537_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_535_);
lean_ctor_set(v___x_500_, 0, v___x_532_);
v___x_537_ = v___x_500_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_535_);
v___x_537_ = v_reuseFailAlloc_541_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_539_; 
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_537_);
v___x_539_ = v___x_527_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
lean_del_object(v___x_505_);
lean_dec(v_snd_503_);
lean_dec(v_fst_502_);
lean_del_object(v___x_500_);
lean_dec(v_a_479_);
lean_dec_ref(v_d_478_);
v_a_574_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_524_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_524_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_del_object(v___x_505_);
lean_dec(v_snd_503_);
lean_dec(v_fst_502_);
lean_del_object(v___x_500_);
lean_dec(v_a_479_);
lean_dec_ref(v_d_478_);
v_a_582_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_513_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_513_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
else
{
lean_object* v___x_590_; 
lean_inc_ref(v___x_508_);
v___x_590_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_508_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = lean_array_fset(v_fst_502_, v_a_479_, v_a_591_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_592_);
v___x_594_ = v___x_505_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_snd_503_);
v___x_594_ = v_reuseFailAlloc_598_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_596_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_594_);
lean_ctor_set(v___x_500_, 0, v___x_507_);
v___x_596_ = v___x_500_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
v_a_492_ = v___x_596_;
goto v___jp_491_;
}
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_del_object(v___x_505_);
lean_dec(v_snd_503_);
lean_dec(v_fst_502_);
lean_del_object(v___x_500_);
lean_dec(v_a_479_);
lean_dec_ref(v_d_478_);
v_a_599_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_590_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_590_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_a_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_del_object(v___x_505_);
lean_dec(v_snd_503_);
lean_dec(v_fst_502_);
lean_del_object(v___x_500_);
lean_dec(v_a_479_);
lean_dec_ref(v_d_478_);
v_a_607_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_510_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_510_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
else
{
uint8_t v___x_615_; 
v___x_615_ = l_Lean_Expr_hasMVar(v___x_508_);
if (v___x_615_ == 0)
{
lean_object* v___x_617_; 
if (v_isShared_506_ == 0)
{
v___x_617_ = v___x_505_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_fst_502_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_snd_503_);
v___x_617_ = v_reuseFailAlloc_621_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_617_);
lean_ctor_set(v___x_500_, 0, v___x_507_);
v___x_619_ = v___x_500_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
v_a_492_ = v___x_619_;
goto v___jp_491_;
}
}
}
else
{
lean_object* v___x_622_; 
lean_inc(v___x_508_);
v___x_622_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_508_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = lean_array_fset(v_fst_502_, v_a_479_, v_a_623_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_624_);
v___x_626_ = v___x_505_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_snd_503_);
v___x_626_ = v_reuseFailAlloc_630_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_628_; 
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 1, v___x_626_);
lean_ctor_set(v___x_500_, 0, v___x_507_);
v___x_628_ = v___x_500_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v_a_492_ = v___x_628_;
goto v___jp_491_;
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_del_object(v___x_505_);
lean_dec(v_snd_503_);
lean_dec(v_fst_502_);
lean_del_object(v___x_500_);
lean_dec(v_a_479_);
lean_dec_ref(v_d_478_);
v_a_631_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_622_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_622_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
}
}
}
v___jp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_add(v_a_479_, v___x_493_);
lean_dec(v_a_479_);
v_a_479_ = v___x_494_;
v_b_480_ = v_a_492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg___boxed(lean_object* v_upperBound_642_, lean_object* v_mvarCounterSaved_643_, lean_object* v_d_644_, lean_object* v_a_645_, lean_object* v_b_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_upperBound_642_, v_mvarCounterSaved_643_, v_d_644_, v_a_645_, v_b_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec(v_mvarCounterSaved_643_);
lean_dec(v_upperBound_642_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object* v_thm_660_, lean_object* v_e_661_, lean_object* v_d_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; lean_object* v_mctx_674_; lean_object* v_expr_675_; lean_object* v_pattern_676_; lean_object* v_rhs_677_; uint8_t v_perm_678_; uint8_t v___x_679_; lean_object* v___x_680_; 
v___x_673_ = lean_st_ref_get(v___y_669_);
v_mctx_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref(v_mctx_674_);
lean_dec(v___x_673_);
v_expr_675_ = lean_ctor_get(v_thm_660_, 0);
lean_inc_ref(v_expr_675_);
v_pattern_676_ = lean_ctor_get(v_thm_660_, 1);
lean_inc_ref_n(v_pattern_676_, 2);
v_rhs_677_ = lean_ctor_get(v_thm_660_, 2);
lean_inc_ref(v_rhs_677_);
v_perm_678_ = lean_ctor_get_uint8(v_thm_660_, sizeof(void*)*3);
lean_dec_ref(v_thm_660_);
v___x_679_ = 1;
lean_inc_ref(v_e_661_);
v___x_680_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_676_, v_e_661_, v___x_679_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_794_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_794_ == 0)
{
v___x_683_ = v___x_680_;
v_isShared_684_ = v_isSharedCheck_794_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_680_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_794_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
if (lean_obj_tag(v_a_681_) == 1)
{
lean_object* v_val_685_; lean_object* v_us_686_; lean_object* v_args_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
lean_del_object(v___x_683_);
v_val_685_ = lean_ctor_get(v_a_681_, 0);
lean_inc(v_val_685_);
lean_dec_ref_known(v_a_681_, 1);
v_us_686_ = lean_ctor_get(v_val_685_, 0);
lean_inc(v_us_686_);
v_args_687_ = lean_ctor_get(v_val_685_, 1);
lean_inc_ref(v_args_687_);
lean_dec(v_val_685_);
v___x_688_ = lean_box(0);
v___x_689_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_us_686_, v___x_688_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v_mvarCounter_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v_mvarCounter_691_ = lean_ctor_get(v_mctx_674_, 3);
lean_inc(v_mvarCounter_691_);
lean_dec_ref(v_mctx_674_);
v___x_692_ = lean_array_get_size(v_args_687_);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = 0;
v___x_695_ = lean_box(0);
v___x_696_ = lean_box(v___x_694_);
v___x_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_697_, 0, v_args_687_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_695_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
v___x_699_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v___x_692_, v_mvarCounter_691_, v_d_662_, v___x_693_, v___x_698_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v_mvarCounter_691_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_773_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_773_ == 0)
{
v___x_702_ = v___x_699_;
v_isShared_703_ = v_isSharedCheck_773_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_699_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_773_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_fst_704_; 
v_fst_704_ = lean_ctor_get(v_a_700_, 0);
if (lean_obj_tag(v_fst_704_) == 0)
{
lean_object* v_snd_705_; lean_object* v_fst_706_; lean_object* v_snd_707_; lean_object* v_levelParams_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_del_object(v___x_702_);
v_snd_705_ = lean_ctor_get(v_a_700_, 1);
lean_inc(v_snd_705_);
lean_dec(v_a_700_);
v_fst_706_ = lean_ctor_get(v_snd_705_, 0);
lean_inc(v_fst_706_);
v_snd_707_ = lean_ctor_get(v_snd_705_, 1);
lean_inc(v_snd_707_);
lean_dec(v_snd_705_);
v_levelParams_708_ = lean_ctor_get(v_pattern_676_, 0);
lean_inc(v_levelParams_708_);
lean_inc(v_a_690_);
v___x_709_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(v_expr_675_, v_pattern_676_, v_a_690_, v_fst_706_);
v___x_710_ = l_Lean_Expr_instantiateLevelParams(v_rhs_677_, v_levelParams_708_, v_a_690_);
lean_dec_ref(v_rhs_677_);
v___x_711_ = l_Lean_Meta_Sym_shareCommonInc(v___x_710_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v___x_713_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_a_712_, v_fst_706_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_752_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_752_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_752_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_752_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
size_t v___x_718_; size_t v___x_719_; uint8_t v___x_720_; 
v___x_718_ = lean_ptr_addr(v_e_661_);
v___x_719_ = lean_ptr_addr(v_a_714_);
v___x_720_ = lean_usize_dec_eq(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_inc(v_a_714_);
v___x_721_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_678_, v_e_661_, v_a_714_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v_a_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_738_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_738_ == 0)
{
v___x_724_ = v___x_721_;
v_isShared_725_ = v_isSharedCheck_738_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_a_722_);
lean_dec(v___x_721_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_738_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
uint8_t v___x_732_; 
v___x_732_ = lean_unbox(v_a_722_);
lean_dec(v_a_722_);
if (v___x_732_ == 0)
{
lean_del_object(v___x_716_);
lean_dec(v_a_714_);
lean_dec_ref(v___x_709_);
goto v___jp_726_;
}
else
{
if (v___x_720_ == 0)
{
lean_object* v___x_733_; uint8_t v___x_734_; lean_object* v___x_736_; 
lean_del_object(v___x_724_);
v___x_733_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_733_, 0, v_a_714_);
lean_ctor_set(v___x_733_, 1, v___x_709_);
lean_ctor_set_uint8(v___x_733_, sizeof(void*)*2, v___x_694_);
v___x_734_ = lean_unbox(v_snd_707_);
lean_dec(v_snd_707_);
lean_ctor_set_uint8(v___x_733_, sizeof(void*)*2 + 1, v___x_734_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_733_);
v___x_736_ = v___x_716_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_733_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
else
{
lean_del_object(v___x_716_);
lean_dec(v_a_714_);
lean_dec_ref(v___x_709_);
goto v___jp_726_;
}
}
v___jp_726_:
{
uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_727_ = lean_unbox(v_snd_707_);
lean_dec(v_snd_707_);
v___x_728_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_727_);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_728_);
v___x_730_ = v___x_724_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_del_object(v___x_716_);
lean_dec(v_a_714_);
lean_dec_ref(v___x_709_);
lean_dec(v_snd_707_);
v_a_739_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_721_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_721_);
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
uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
lean_dec(v_a_714_);
lean_dec_ref(v___x_709_);
lean_dec_ref(v_e_661_);
v___x_747_ = lean_unbox(v_snd_707_);
lean_dec(v_snd_707_);
v___x_748_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_747_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_748_);
v___x_750_ = v___x_716_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
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
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v___x_709_);
lean_dec(v_snd_707_);
lean_dec_ref(v_e_661_);
v_a_753_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_713_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_713_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___x_709_);
lean_dec(v_snd_707_);
lean_dec(v_fst_706_);
lean_dec_ref(v_e_661_);
v_a_761_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_711_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_711_);
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
lean_object* v_val_769_; lean_object* v___x_771_; 
lean_inc_ref(v_fst_704_);
lean_dec(v_a_700_);
lean_dec(v_a_690_);
lean_dec_ref(v_rhs_677_);
lean_dec_ref(v_pattern_676_);
lean_dec_ref(v_expr_675_);
lean_dec_ref(v_e_661_);
v_val_769_ = lean_ctor_get(v_fst_704_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v_fst_704_, 1);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v_val_769_);
v___x_771_ = v___x_702_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_val_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v_a_690_);
lean_dec_ref(v_rhs_677_);
lean_dec_ref(v_pattern_676_);
lean_dec_ref(v_expr_675_);
lean_dec_ref(v_e_661_);
v_a_774_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_699_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_699_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_object* v_a_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_789_; 
lean_dec_ref(v_args_687_);
lean_dec_ref(v_rhs_677_);
lean_dec_ref(v_pattern_676_);
lean_dec_ref(v_expr_675_);
lean_dec_ref(v_mctx_674_);
lean_dec_ref(v_d_662_);
lean_dec_ref(v_e_661_);
v_a_782_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_789_ == 0)
{
v___x_784_ = v___x_689_;
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_a_782_);
lean_dec(v___x_689_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_789_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_787_; 
if (v_isShared_785_ == 0)
{
v___x_787_ = v___x_784_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
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
lean_object* v___x_790_; lean_object* v___x_792_; 
lean_dec(v_a_681_);
lean_dec_ref(v_rhs_677_);
lean_dec_ref(v_pattern_676_);
lean_dec_ref(v_expr_675_);
lean_dec_ref(v_mctx_674_);
lean_dec_ref(v_d_662_);
lean_dec_ref(v_e_661_);
v___x_790_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0));
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_790_);
v___x_792_ = v___x_683_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_rhs_677_);
lean_dec_ref(v_pattern_676_);
lean_dec_ref(v_expr_675_);
lean_dec_ref(v_mctx_674_);
lean_dec_ref(v_d_662_);
lean_dec_ref(v_e_661_);
v_a_795_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_680_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_680_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object* v_thm_803_, lean_object* v_e_804_, lean_object* v_d_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(v_thm_803_, v_e_804_, v_d_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object* v_thm_817_, lean_object* v_e_818_, lean_object* v_d_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v___f_830_; uint8_t v___x_831_; lean_object* v___x_832_; 
v___f_830_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed), 13, 3);
lean_closure_set(v___f_830_, 0, v_thm_817_);
lean_closure_set(v___f_830_, 1, v_e_818_);
lean_closure_set(v___f_830_, 2, v_d_819_);
v___x_831_ = 0;
v___x_832_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v___f_830_, v___x_831_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object* v_thm_833_, lean_object* v_e_834_, lean_object* v_d_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_thm_833_, v_e_834_, v_d_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(lean_object* v_mvarId_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_847_, v___y_854_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(lean_object* v_mvarId_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(v_mvarId_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec(v_mvarId_859_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(lean_object* v_mvarId_871_, lean_object* v_val_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_871_, v_val_872_, v___y_879_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(lean_object* v_mvarId_884_, lean_object* v_val_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(v_mvarId_884_, v_val_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(lean_object* v_upperBound_897_, lean_object* v_mvarCounterSaved_898_, lean_object* v_d_899_, lean_object* v___x_900_, lean_object* v_inst_901_, lean_object* v_R_902_, lean_object* v_a_903_, lean_object* v_b_904_, lean_object* v_c_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_upperBound_897_, v_mvarCounterSaved_898_, v_d_899_, v_a_903_, v_b_904_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___boxed(lean_object** _args){
lean_object* v_upperBound_917_ = _args[0];
lean_object* v_mvarCounterSaved_918_ = _args[1];
lean_object* v_d_919_ = _args[2];
lean_object* v___x_920_ = _args[3];
lean_object* v_inst_921_ = _args[4];
lean_object* v_R_922_ = _args[5];
lean_object* v_a_923_ = _args[6];
lean_object* v_b_924_ = _args[7];
lean_object* v_c_925_ = _args[8];
lean_object* v___y_926_ = _args[9];
lean_object* v___y_927_ = _args[10];
lean_object* v___y_928_ = _args[11];
lean_object* v___y_929_ = _args[12];
lean_object* v___y_930_ = _args[13];
lean_object* v___y_931_ = _args[14];
lean_object* v___y_932_ = _args[15];
lean_object* v___y_933_ = _args[16];
lean_object* v___y_934_ = _args[17];
lean_object* v___y_935_ = _args[18];
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(v_upperBound_917_, v_mvarCounterSaved_918_, v_d_919_, v___x_920_, v_inst_921_, v_R_922_, v_a_923_, v_b_924_, v_c_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec(v___x_920_);
lean_dec(v_mvarCounterSaved_918_);
lean_dec(v_upperBound_917_);
return v_res_936_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_object* v_00_u03b2_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
uint8_t v___x_940_; 
v___x_940_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_938_, v_x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(lean_object* v_00_u03b2_941_, lean_object* v_x_942_, lean_object* v_x_943_){
_start:
{
uint8_t v_res_944_; lean_object* v_r_945_; 
v_res_944_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(v_00_u03b2_941_, v_x_942_, v_x_943_);
lean_dec(v_x_943_);
lean_dec_ref(v_x_942_);
v_r_945_ = lean_box(v_res_944_);
return v_r_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(lean_object* v_00_u03b2_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_x_947_, v_x_948_, v_x_949_);
return v___x_950_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(lean_object* v_00_u03b2_951_, lean_object* v_x_952_, size_t v_x_953_, lean_object* v_x_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___redArg(v_x_952_, v_x_953_, v_x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4___boxed(lean_object* v_00_u03b2_956_, lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
size_t v_x_41623__boxed_960_; uint8_t v_res_961_; lean_object* v_r_962_; 
v_x_41623__boxed_960_ = lean_unbox_usize(v_x_958_);
lean_dec(v_x_958_);
v_res_961_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4(v_00_u03b2_956_, v_x_957_, v_x_41623__boxed_960_, v_x_959_);
lean_dec(v_x_959_);
lean_dec_ref(v_x_957_);
v_r_962_ = lean_box(v_res_961_);
return v_r_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_963_, lean_object* v_x_964_, size_t v_x_965_, size_t v_x_966_, lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___redArg(v_x_964_, v_x_965_, v_x_966_, v_x_967_, v_x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_970_, lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_x_973_, lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
size_t v_x_41634__boxed_976_; size_t v_x_41635__boxed_977_; lean_object* v_res_978_; 
v_x_41634__boxed_976_ = lean_unbox_usize(v_x_972_);
lean_dec(v_x_972_);
v_x_41635__boxed_977_ = lean_unbox_usize(v_x_973_);
lean_dec(v_x_973_);
v_res_978_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7(v_00_u03b2_970_, v_x_971_, v_x_41634__boxed_976_, v_x_41635__boxed_977_, v_x_974_, v_x_975_);
return v_res_978_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(lean_object* v_00_u03b2_979_, lean_object* v_keys_980_, lean_object* v_vals_981_, lean_object* v_heq_982_, lean_object* v_i_983_, lean_object* v_k_984_){
_start:
{
uint8_t v___x_985_; 
v___x_985_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___redArg(v_keys_980_, v_i_983_, v_k_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7___boxed(lean_object* v_00_u03b2_986_, lean_object* v_keys_987_, lean_object* v_vals_988_, lean_object* v_heq_989_, lean_object* v_i_990_, lean_object* v_k_991_){
_start:
{
uint8_t v_res_992_; lean_object* v_r_993_; 
v_res_992_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__4_spec__7(v_00_u03b2_986_, v_keys_987_, v_vals_988_, v_heq_989_, v_i_990_, v_k_991_);
lean_dec(v_k_991_);
lean_dec_ref(v_vals_988_);
lean_dec_ref(v_keys_987_);
v_r_993_ = lean_box(v_res_992_);
return v_r_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_994_, lean_object* v_n_995_, lean_object* v_k_996_, lean_object* v_v_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10___redArg(v_n_995_, v_k_996_, v_v_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_999_, size_t v_depth_1000_, lean_object* v_keys_1001_, lean_object* v_vals_1002_, lean_object* v_heq_1003_, lean_object* v_i_1004_, lean_object* v_entries_1005_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___redArg(v_depth_1000_, v_keys_1001_, v_vals_1002_, v_i_1004_, v_entries_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1007_, lean_object* v_depth_1008_, lean_object* v_keys_1009_, lean_object* v_vals_1010_, lean_object* v_heq_1011_, lean_object* v_i_1012_, lean_object* v_entries_1013_){
_start:
{
size_t v_depth_boxed_1014_; lean_object* v_res_1015_; 
v_depth_boxed_1014_ = lean_unbox_usize(v_depth_1008_);
lean_dec(v_depth_1008_);
v_res_1015_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_1007_, v_depth_boxed_1014_, v_keys_1009_, v_vals_1010_, v_heq_1011_, v_i_1012_, v_entries_1013_);
lean_dec_ref(v_vals_1010_);
lean_dec_ref(v_keys_1009_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11(lean_object* v_00_u03b2_1016_, lean_object* v_x_1017_, lean_object* v_x_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__7_spec__10_spec__11___redArg(v_x_1017_, v_x_1018_, v_x_1019_, v_x_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(lean_object* v_fst_1022_, lean_object* v_d_1023_, lean_object* v_x_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v___x_1035_; 
v___x_1035_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1022_, v_x_1024_, v_d_1023_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed(lean_object* v_fst_1036_, lean_object* v_d_1037_, lean_object* v_x_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(v_fst_1036_, v_d_1037_, v_x_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object* v_d_1050_, lean_object* v_e_1051_, lean_object* v_as_1052_, size_t v_sz_1053_, size_t v_i_1054_, lean_object* v_b_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
uint8_t v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1074_; uint8_t v___y_1075_; uint8_t v___y_1076_; uint8_t v___y_1079_; lean_object* v___y_1080_; uint8_t v___y_1081_; uint8_t v___y_1082_; lean_object* v___y_1084_; uint8_t v___y_1085_; uint8_t v___y_1086_; lean_object* v___y_1090_; uint8_t v___y_1091_; uint8_t v___x_1093_; 
v___x_1093_ = lean_usize_dec_lt(v_i_1054_, v_sz_1053_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec_ref(v_e_1051_);
lean_dec_ref(v_d_1050_);
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v_b_1055_);
return v___x_1094_;
}
else
{
lean_object* v_a_1095_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v_snd_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1147_; 
v_a_1095_ = lean_array_uget_borrowed(v_as_1052_, v_i_1054_);
v_fst_1096_ = lean_ctor_get(v_a_1095_, 0);
v_snd_1097_ = lean_ctor_get(v_a_1095_, 1);
v_snd_1098_ = lean_ctor_get(v_b_1055_, 1);
v_isSharedCheck_1147_ = !lean_is_exclusive(v_b_1055_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; 
v_unused_1148_ = lean_ctor_get(v_b_1055_, 0);
lean_dec(v_unused_1148_);
v___x_1100_ = v_b_1055_;
v_isShared_1101_ = v_isSharedCheck_1147_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_snd_1098_);
lean_dec(v_b_1055_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1147_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1102_; lean_object* v___y_1104_; uint8_t v_done_1105_; uint8_t v___y_1106_; lean_object* v_result_1116_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1102_ = lean_box(0);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_nat_dec_eq(v_snd_1097_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___f_1126_; lean_object* v___x_1127_; 
lean_inc_ref(v_d_1050_);
lean_inc(v_fst_1096_);
v___f_1126_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1126_, 0, v_fst_1096_);
lean_closure_set(v___f_1126_, 1, v_d_1050_);
lean_inc_ref(v_e_1051_);
v___x_1127_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_1051_, v_snd_1097_, v___f_1126_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v_result_1116_ = v_a_1128_;
goto v___jp_1115_;
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_del_object(v___x_1100_);
lean_dec(v_snd_1098_);
lean_dec_ref(v_e_1051_);
lean_dec_ref(v_d_1050_);
v_a_1129_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1127_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1127_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v___x_1137_; 
lean_inc_ref(v_d_1050_);
lean_inc_ref(v_e_1051_);
lean_inc(v_fst_1096_);
v___x_1137_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1096_, v_e_1051_, v_d_1050_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v_result_1116_ = v_a_1138_;
goto v___jp_1115_;
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_del_object(v___x_1100_);
lean_dec(v_snd_1098_);
lean_dec_ref(v_e_1051_);
lean_dec_ref(v_d_1050_);
v_a_1139_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1137_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1137_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
v___jp_1103_:
{
if (v_done_1105_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
lean_dec_ref(v___y_1104_);
v___x_1107_ = lean_box(v___y_1106_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 1, v___x_1107_);
lean_ctor_set(v___x_1100_, 0, v___x_1102_);
v___x_1109_ = v___x_1100_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v___x_1107_);
v___x_1109_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
size_t v___x_1110_; size_t v___x_1111_; 
v___x_1110_ = ((size_t)1ULL);
v___x_1111_ = lean_usize_add(v_i_1054_, v___x_1110_);
v_i_1054_ = v___x_1111_;
v_b_1055_ = v___x_1109_;
goto _start;
}
}
else
{
uint8_t v___x_1114_; 
lean_del_object(v___x_1100_);
lean_dec_ref(v_e_1051_);
lean_dec_ref(v_d_1050_);
v___x_1114_ = 0;
v___y_1084_ = v___y_1104_;
v___y_1085_ = v___y_1106_;
v___y_1086_ = v___x_1114_;
goto v___jp_1083_;
}
}
v___jp_1115_:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_unbox(v_snd_1098_);
if (v___x_1117_ == 0)
{
lean_dec(v_snd_1098_);
if (lean_obj_tag(v_result_1116_) == 0)
{
uint8_t v_done_1118_; uint8_t v_contextDependent_1119_; 
v_done_1118_ = lean_ctor_get_uint8(v_result_1116_, 0);
v_contextDependent_1119_ = lean_ctor_get_uint8(v_result_1116_, 1);
v___y_1104_ = v_result_1116_;
v_done_1105_ = v_done_1118_;
v___y_1106_ = v_contextDependent_1119_;
goto v___jp_1103_;
}
else
{
uint8_t v_contextDependent_1120_; 
lean_del_object(v___x_1100_);
lean_dec_ref(v_e_1051_);
lean_dec_ref(v_d_1050_);
v_contextDependent_1120_ = lean_ctor_get_uint8(v_result_1116_, sizeof(void*)*2 + 1);
v___y_1090_ = v_result_1116_;
v___y_1091_ = v_contextDependent_1120_;
goto v___jp_1089_;
}
}
else
{
if (lean_obj_tag(v_result_1116_) == 0)
{
uint8_t v_done_1121_; uint8_t v___x_1122_; 
v_done_1121_ = lean_ctor_get_uint8(v_result_1116_, 0);
v___x_1122_ = lean_unbox(v_snd_1098_);
lean_dec(v_snd_1098_);
v___y_1104_ = v_result_1116_;
v_done_1105_ = v_done_1121_;
v___y_1106_ = v___x_1122_;
goto v___jp_1103_;
}
else
{
uint8_t v___x_1123_; 
lean_del_object(v___x_1100_);
lean_dec_ref(v_e_1051_);
lean_dec_ref(v_d_1050_);
v___x_1123_ = lean_unbox(v_snd_1098_);
lean_dec(v_snd_1098_);
v___y_1090_ = v_result_1116_;
v___y_1091_ = v___x_1123_;
goto v___jp_1089_;
}
}
}
}
}
v___jp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___y_1068_);
v___x_1070_ = lean_box(v___y_1067_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
v___jp_1073_:
{
if (v___y_1076_ == 0)
{
v___y_1067_ = v___y_1075_;
v___y_1068_ = v___y_1074_;
goto v___jp_1066_;
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1074_);
v___y_1067_ = v___y_1075_;
v___y_1068_ = v___x_1077_;
goto v___jp_1066_;
}
}
v___jp_1078_:
{
if (v___y_1082_ == 0)
{
v___y_1074_ = v___y_1080_;
v___y_1075_ = v___y_1081_;
v___y_1076_ = v___y_1081_;
goto v___jp_1073_;
}
else
{
v___y_1074_ = v___y_1080_;
v___y_1075_ = v___y_1081_;
v___y_1076_ = v___y_1079_;
goto v___jp_1073_;
}
}
v___jp_1083_:
{
if (v___y_1085_ == 0)
{
v___y_1067_ = v___y_1085_;
v___y_1068_ = v___y_1084_;
goto v___jp_1066_;
}
else
{
if (lean_obj_tag(v___y_1084_) == 0)
{
uint8_t v_contextDependent_1087_; 
v_contextDependent_1087_ = lean_ctor_get_uint8(v___y_1084_, 1);
v___y_1079_ = v___y_1086_;
v___y_1080_ = v___y_1084_;
v___y_1081_ = v___y_1085_;
v___y_1082_ = v_contextDependent_1087_;
goto v___jp_1078_;
}
else
{
uint8_t v_contextDependent_1088_; 
v_contextDependent_1088_ = lean_ctor_get_uint8(v___y_1084_, sizeof(void*)*2 + 1);
v___y_1079_ = v___y_1086_;
v___y_1080_ = v___y_1084_;
v___y_1081_ = v___y_1085_;
v___y_1082_ = v_contextDependent_1088_;
goto v___jp_1078_;
}
}
}
v___jp_1089_:
{
uint8_t v___x_1092_; 
v___x_1092_ = 0;
v___y_1084_ = v___y_1090_;
v___y_1085_ = v___y_1091_;
v___y_1086_ = v___x_1092_;
goto v___jp_1083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object* v_d_1149_, lean_object* v_e_1150_, lean_object* v_as_1151_, lean_object* v_sz_1152_, lean_object* v_i_1153_, lean_object* v_b_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
size_t v_sz_boxed_1165_; size_t v_i_boxed_1166_; lean_object* v_res_1167_; 
v_sz_boxed_1165_ = lean_unbox_usize(v_sz_1152_);
lean_dec(v_sz_1152_);
v_i_boxed_1166_ = lean_unbox_usize(v_i_1153_);
lean_dec(v_i_1153_);
v_res_1167_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1149_, v_e_1150_, v_as_1151_, v_sz_boxed_1165_, v_i_boxed_1166_, v_b_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v_as_1151_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object* v_thms_1172_, lean_object* v_d_1173_, lean_object* v_e_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; size_t v_sz_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
v___x_1185_ = l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(v_thms_1172_, v_e_1174_);
v___x_1186_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0));
v_sz_1187_ = lean_array_size(v___x_1185_);
v___x_1188_ = ((size_t)0ULL);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1173_, v_e_1174_, v___x_1185_, v_sz_1187_, v___x_1188_, v___x_1186_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec_ref(v___x_1185_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1205_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1205_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1205_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_fst_1194_; 
v_fst_1194_ = lean_ctor_get(v_a_1190_, 0);
if (lean_obj_tag(v_fst_1194_) == 0)
{
lean_object* v_snd_1195_; uint8_t v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v_snd_1195_ = lean_ctor_get(v_a_1190_, 1);
lean_inc(v_snd_1195_);
lean_dec(v_a_1190_);
v___x_1196_ = lean_unbox(v_snd_1195_);
lean_dec(v_snd_1195_);
v___x_1197_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1196_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1197_);
v___x_1199_ = v___x_1192_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
lean_object* v_val_1201_; lean_object* v___x_1203_; 
lean_inc_ref(v_fst_1194_);
lean_dec(v_a_1190_);
v_val_1201_ = lean_ctor_get(v_fst_1194_, 0);
lean_inc(v_val_1201_);
lean_dec_ref_known(v_fst_1194_, 1);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v_val_1201_);
v___x_1203_ = v___x_1192_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_val_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
v_a_1206_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1189_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1189_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object* v_thms_1214_, lean_object* v_d_1215_, lean_object* v_e_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_thms_1214_, v_d_1215_, v_e_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_thms_1214_);
return v_res_1227_;
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
