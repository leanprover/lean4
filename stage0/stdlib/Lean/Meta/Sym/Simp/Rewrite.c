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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Pattern_match_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkRflResultCD(uint8_t);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Meta_acLt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpOverApplied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_getFallbackMatchWithExtra(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(uint8_t v_perm_18_, lean_object* v_e_19_, lean_object* v_result_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
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
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm_0interp(lean_interpreter_value* stack)
{
uint8_t v_perm_18_ = stack[0].m_num;
lean_object* v_e_19_ = stack[1].m_obj;
lean_object* v_result_20_ = stack[2].m_obj;
lean_object* v_a_21_ = stack[3].m_obj;
lean_object* v_a_22_ = stack[4].m_obj;
lean_object* v_a_23_ = stack[5].m_obj;
lean_object* v_a_24_ = stack[6].m_obj;
lean_object* v_res_31_;
v_res_31_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_18_, v_e_19_, v_result_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm___boxed(lean_object* v_perm_32_, lean_object* v_e_33_, lean_object* v_result_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
uint8_t v_perm_boxed_40_; lean_object* v_res_41_; 
v_perm_boxed_40_ = lean_unbox(v_perm_32_);
v_res_41_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_boxed_40_, v_e_33_, v_result_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
return v_res_41_;
}
}
lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(lean_object* v_l_42_, lean_object* v___y_43_){
_start:
{
lean_object* v___x_45_; lean_object* v_mctx_46_; lean_object* v___x_47_; lean_object* v_fst_48_; lean_object* v_snd_49_; lean_object* v___x_50_; lean_object* v_cache_51_; lean_object* v_zetaDeltaFVarIds_52_; lean_object* v_postponed_53_; lean_object* v_diag_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_63_; 
v___x_45_ = lean_st_ref_get(v___y_43_);
v_mctx_46_ = lean_ctor_get(v___x_45_, 0);
lean_inc_ref(v_mctx_46_);
lean_dec(v___x_45_);
v___x_47_ = lean_instantiate_level_mvars(v_mctx_46_, v_l_42_);
v_fst_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_fst_48_);
v_snd_49_ = lean_ctor_get(v___x_47_, 1);
lean_inc(v_snd_49_);
lean_dec_ref(v___x_47_);
v___x_50_ = lean_st_ref_take(v___y_43_);
v_cache_51_ = lean_ctor_get(v___x_50_, 1);
v_zetaDeltaFVarIds_52_ = lean_ctor_get(v___x_50_, 2);
v_postponed_53_ = lean_ctor_get(v___x_50_, 3);
v_diag_54_ = lean_ctor_get(v___x_50_, 4);
v_isSharedCheck_63_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_63_ == 0)
{
lean_object* v_unused_64_; 
v_unused_64_ = lean_ctor_get(v___x_50_, 0);
lean_dec(v_unused_64_);
v___x_56_ = v___x_50_;
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_diag_54_);
lean_inc(v_postponed_53_);
lean_inc(v_zetaDeltaFVarIds_52_);
lean_inc(v_cache_51_);
lean_dec(v___x_50_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_63_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 0, v_fst_48_);
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_fst_48_);
lean_ctor_set(v_reuseFailAlloc_62_, 1, v_cache_51_);
lean_ctor_set(v_reuseFailAlloc_62_, 2, v_zetaDeltaFVarIds_52_);
lean_ctor_set(v_reuseFailAlloc_62_, 3, v_postponed_53_);
lean_ctor_set(v_reuseFailAlloc_62_, 4, v_diag_54_);
v___x_59_ = v_reuseFailAlloc_62_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_st_ref_put(v___y_43_, v___x_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v_snd_49_);
return v___x_61_;
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_42_ = stack[0].m_obj;
lean_object* v___y_43_ = stack[1].m_obj;
lean_object* v_res_65_;
v_res_65_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_l_42_, v___y_43_);
stack->m_obj
 = v_res_65_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg___boxed(lean_object* v_l_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_l_66_, v___y_67_);
lean_dec(v___y_67_);
return v_res_69_;
}
}
lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(lean_object* v_l_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_l_70_, v___y_77_);
return v___x_81_;
}
}
LEAN_EXPORT void l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_l_70_ = stack[0].m_obj;
lean_object* v___y_71_ = stack[1].m_obj;
lean_object* v___y_72_ = stack[2].m_obj;
lean_object* v___y_73_ = stack[3].m_obj;
lean_object* v___y_74_ = stack[4].m_obj;
lean_object* v___y_75_ = stack[5].m_obj;
lean_object* v___y_76_ = stack[6].m_obj;
lean_object* v___y_77_ = stack[7].m_obj;
lean_object* v___y_78_ = stack[8].m_obj;
lean_object* v___y_79_ = stack[9].m_obj;
lean_object* v_res_82_;
v_res_82_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(v_l_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___boxed(lean_object* v_l_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0(v_l_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
return v_res_94_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(lean_object* v_e_95_, lean_object* v___y_96_){
_start:
{
uint8_t v___x_98_; 
v___x_98_ = l_Lean_Expr_hasMVar(v_e_95_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v_e_95_);
return v___x_99_;
}
else
{
lean_object* v___x_100_; lean_object* v_mctx_101_; lean_object* v___x_102_; lean_object* v_fst_103_; lean_object* v_snd_104_; lean_object* v___x_105_; lean_object* v_cache_106_; lean_object* v_zetaDeltaFVarIds_107_; lean_object* v_postponed_108_; lean_object* v_diag_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_118_; 
v___x_100_ = lean_st_ref_get(v___y_96_);
v_mctx_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc_ref(v_mctx_101_);
lean_dec(v___x_100_);
v___x_102_ = l_Lean_instantiateMVarsCore(v_mctx_101_, v_e_95_);
v_fst_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_fst_103_);
v_snd_104_ = lean_ctor_get(v___x_102_, 1);
lean_inc(v_snd_104_);
lean_dec_ref(v___x_102_);
v___x_105_ = lean_st_ref_take(v___y_96_);
v_cache_106_ = lean_ctor_get(v___x_105_, 1);
v_zetaDeltaFVarIds_107_ = lean_ctor_get(v___x_105_, 2);
v_postponed_108_ = lean_ctor_get(v___x_105_, 3);
v_diag_109_ = lean_ctor_get(v___x_105_, 4);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; 
v_unused_119_ = lean_ctor_get(v___x_105_, 0);
lean_dec(v_unused_119_);
v___x_111_ = v___x_105_;
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_diag_109_);
lean_inc(v_postponed_108_);
lean_inc(v_zetaDeltaFVarIds_107_);
lean_inc(v_cache_106_);
lean_dec(v___x_105_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_118_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v_snd_104_);
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_snd_104_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_cache_106_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v_zetaDeltaFVarIds_107_);
lean_ctor_set(v_reuseFailAlloc_117_, 3, v_postponed_108_);
lean_ctor_set(v_reuseFailAlloc_117_, 4, v_diag_109_);
v___x_114_ = v_reuseFailAlloc_117_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_st_ref_put(v___y_96_, v___x_114_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v_fst_103_);
return v___x_116_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_95_ = stack[0].m_obj;
lean_object* v___y_96_ = stack[1].m_obj;
lean_object* v_res_120_;
v_res_120_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_e_95_, v___y_96_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg___boxed(lean_object* v_e_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_e_121_, v___y_122_);
lean_dec(v___y_122_);
return v_res_124_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(lean_object* v_e_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_e_125_, v___y_132_);
return v___x_136_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_125_ = stack[0].m_obj;
lean_object* v___y_126_ = stack[1].m_obj;
lean_object* v___y_127_ = stack[2].m_obj;
lean_object* v___y_128_ = stack[3].m_obj;
lean_object* v___y_129_ = stack[4].m_obj;
lean_object* v___y_130_ = stack[5].m_obj;
lean_object* v___y_131_ = stack[6].m_obj;
lean_object* v___y_132_ = stack[7].m_obj;
lean_object* v___y_133_ = stack[8].m_obj;
lean_object* v___y_134_ = stack[9].m_obj;
lean_object* v_res_137_;
v_res_137_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(v_e_125_, v___y_126_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___boxed(lean_object* v_e_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(v_e_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
lean_dec(v___y_141_);
lean_dec_ref(v___y_140_);
lean_dec(v___y_139_);
return v_res_149_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0(lean_object* v_k_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; 
lean_inc(v___y_155_);
lean_inc_ref(v___y_154_);
lean_inc(v___y_153_);
lean_inc_ref(v___y_152_);
lean_inc(v___y_151_);
v___x_161_ = lean_apply_10(v_k_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_, lean_box(0));
return v___x_161_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_150_ = stack[0].m_obj;
lean_object* v___y_151_ = stack[1].m_obj;
lean_object* v___y_152_ = stack[2].m_obj;
lean_object* v___y_153_ = stack[3].m_obj;
lean_object* v___y_154_ = stack[4].m_obj;
lean_object* v___y_155_ = stack[5].m_obj;
lean_object* v___y_156_ = stack[6].m_obj;
lean_object* v___y_157_ = stack[7].m_obj;
lean_object* v___y_158_ = stack[8].m_obj;
lean_object* v___y_159_ = stack[9].m_obj;
lean_object* v_res_162_;
v_res_162_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0(v_k_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0___boxed(lean_object* v_k_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0(v_k_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
return v_res_174_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(lean_object* v_k_175_, uint8_t v_allowLevelAssignments_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v___f_187_; lean_object* v___x_188_; 
lean_inc(v___y_181_);
lean_inc_ref(v___y_180_);
lean_inc(v___y_179_);
lean_inc_ref(v___y_178_);
lean_inc(v___y_177_);
v___f_187_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_187_, 0, v_k_175_);
lean_closure_set(v___f_187_, 1, v___y_177_);
lean_closure_set(v___f_187_, 2, v___y_178_);
lean_closure_set(v___f_187_, 3, v___y_179_);
lean_closure_set(v___f_187_, 4, v___y_180_);
lean_closure_set(v___f_187_, 5, v___y_181_);
v___x_188_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_176_, v___f_187_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
if (lean_obj_tag(v___x_188_) == 0)
{
return v___x_188_;
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_175_ = stack[0].m_obj;
uint8_t v_allowLevelAssignments_176_ = stack[1].m_num;
lean_object* v___y_177_ = stack[2].m_obj;
lean_object* v___y_178_ = stack[3].m_obj;
lean_object* v___y_179_ = stack[4].m_obj;
lean_object* v___y_180_ = stack[5].m_obj;
lean_object* v___y_181_ = stack[6].m_obj;
lean_object* v___y_182_ = stack[7].m_obj;
lean_object* v___y_183_ = stack[8].m_obj;
lean_object* v___y_184_ = stack[9].m_obj;
lean_object* v___y_185_ = stack[10].m_obj;
lean_object* v_res_197_;
v_res_197_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(v_k_175_, v_allowLevelAssignments_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___boxed(lean_object* v_k_198_, lean_object* v_allowLevelAssignments_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_210_; lean_object* v_res_211_; 
v_allowLevelAssignments_boxed_210_ = lean_unbox(v_allowLevelAssignments_199_);
v_res_211_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(v_k_198_, v_allowLevelAssignments_boxed_210_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
lean_dec(v___y_200_);
return v_res_211_;
}
}
lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6(lean_object* v_00_u03b1_212_, lean_object* v_k_213_, uint8_t v_allowLevelAssignments_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(v_k_213_, v_allowLevelAssignments_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
return v___x_225_;
}
}
LEAN_EXPORT void l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_213_ = stack[1].m_obj;
uint8_t v_allowLevelAssignments_214_ = stack[2].m_num;
lean_object* v___y_215_ = stack[3].m_obj;
lean_object* v___y_216_ = stack[4].m_obj;
lean_object* v___y_217_ = stack[5].m_obj;
lean_object* v___y_218_ = stack[6].m_obj;
lean_object* v___y_219_ = stack[7].m_obj;
lean_object* v___y_220_ = stack[8].m_obj;
lean_object* v___y_221_ = stack[9].m_obj;
lean_object* v___y_222_ = stack[10].m_obj;
lean_object* v___y_223_ = stack[11].m_obj;
lean_object* v_res_226_;
v_res_226_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6(lean_box(0), v_k_213_, v_allowLevelAssignments_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
stack->m_obj
 = v_res_226_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___boxed(lean_object* v_00_u03b1_227_, lean_object* v_k_228_, lean_object* v_allowLevelAssignments_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_240_; lean_object* v_res_241_; 
v_allowLevelAssignments_boxed_240_ = lean_unbox(v_allowLevelAssignments_229_);
v_res_241_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6(v_00_u03b1_227_, v_k_228_, v_allowLevelAssignments_boxed_240_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v___y_230_);
return v_res_241_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(lean_object* v_keys_242_, lean_object* v_i_243_, lean_object* v_k_244_){
_start:
{
lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_array_get_size(v_keys_242_);
v___x_246_ = lean_nat_dec_lt(v_i_243_, v___x_245_);
if (v___x_246_ == 0)
{
lean_dec(v_i_243_);
return v___x_246_;
}
else
{
lean_object* v_k_x27_247_; uint8_t v___x_248_; 
v_k_x27_247_ = lean_array_fget_borrowed(v_keys_242_, v_i_243_);
v___x_248_ = l_Lean_instBEqMVarId_beq(v_k_244_, v_k_x27_247_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_add(v_i_243_, v___x_249_);
lean_dec(v_i_243_);
v_i_243_ = v___x_250_;
goto _start;
}
else
{
lean_dec(v_i_243_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_242_ = stack[0].m_obj;
lean_object* v_i_243_ = stack[1].m_obj;
lean_object* v_k_244_ = stack[2].m_obj;
uint8_t v_res_252_;
v_res_252_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_keys_242_, v_i_243_, v_k_244_);
stack->m_num = v_res_252_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_keys_253_, lean_object* v_i_254_, lean_object* v_k_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_keys_253_, v_i_254_, v_k_255_);
lean_dec(v_k_255_);
lean_dec_ref(v_keys_253_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(lean_object* v_x_258_, size_t v_x_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
lean_object* v_es_261_; lean_object* v___x_262_; size_t v___x_263_; size_t v___x_264_; lean_object* v_j_265_; lean_object* v___x_266_; 
v_es_261_ = lean_ctor_get(v_x_258_, 0);
v___x_262_ = lean_box(2);
v___x_263_ = ((size_t)31ULL);
v___x_264_ = lean_usize_land(v_x_259_, v___x_263_);
v_j_265_ = lean_usize_to_nat(v___x_264_);
v___x_266_ = lean_array_get_borrowed(v___x_262_, v_es_261_, v_j_265_);
lean_dec(v_j_265_);
switch(lean_obj_tag(v___x_266_))
{
case 0:
{
lean_object* v_key_267_; uint8_t v___x_268_; 
v_key_267_ = lean_ctor_get(v___x_266_, 0);
v___x_268_ = l_Lean_instBEqMVarId_beq(v_x_260_, v_key_267_);
return v___x_268_;
}
case 1:
{
lean_object* v_node_269_; size_t v___x_270_; size_t v___x_271_; 
v_node_269_ = lean_ctor_get(v___x_266_, 0);
v___x_270_ = ((size_t)5ULL);
v___x_271_ = lean_usize_shift_right(v_x_259_, v___x_270_);
v_x_258_ = v_node_269_;
v_x_259_ = v___x_271_;
goto _start;
}
default: 
{
uint8_t v___x_273_; 
v___x_273_ = 0;
return v___x_273_;
}
}
}
else
{
lean_object* v_ks_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_ks_274_ = lean_ctor_get(v_x_258_, 0);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_276_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_ks_274_, v___x_275_, v_x_260_);
return v___x_276_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_258_ = stack[0].m_obj;
size_t v_x_259_ = stack[1].m_num;
lean_object* v_x_260_ = stack[2].m_obj;
uint8_t v_res_277_;
v_res_277_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_258_, v_x_259_, v_x_260_);
stack->m_num = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_x_278_, lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
size_t v_x_44079__boxed_281_; uint8_t v_res_282_; lean_object* v_r_283_; 
v_x_44079__boxed_281_ = lean_unbox_usize(v_x_279_);
lean_dec(v_x_279_);
v_res_282_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_278_, v_x_44079__boxed_281_, v_x_280_);
lean_dec(v_x_280_);
lean_dec_ref(v_x_278_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
uint64_t v___x_286_; size_t v___x_287_; uint8_t v___x_288_; 
v___x_286_ = l_Lean_instHashableMVarId_hash(v_x_285_);
v___x_287_ = lean_uint64_to_usize(v___x_286_);
v___x_288_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_284_, v___x_287_, v_x_285_);
return v___x_288_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_284_ = stack[0].m_obj;
lean_object* v_x_285_ = stack[1].m_obj;
uint8_t v_res_289_;
v_res_289_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_284_, v_x_285_);
stack->m_num = v_res_289_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg___boxed(lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_290_, v_x_291_);
lean_dec(v_x_291_);
lean_dec_ref(v_x_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(lean_object* v_mvarId_294_, lean_object* v___y_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_mctx_298_; lean_object* v_eAssignment_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_297_ = lean_st_ref_get(v___y_295_);
v_mctx_298_ = lean_ctor_get(v___x_297_, 0);
lean_inc_ref(v_mctx_298_);
lean_dec(v___x_297_);
v_eAssignment_299_ = lean_ctor_get(v_mctx_298_, 8);
lean_inc_ref(v_eAssignment_299_);
lean_dec_ref(v_mctx_298_);
v___x_300_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_eAssignment_299_, v_mvarId_294_);
lean_dec_ref(v_eAssignment_299_);
v___x_301_ = lean_box(v___x_300_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_294_ = stack[0].m_obj;
lean_object* v___y_295_ = stack[1].m_obj;
lean_object* v_res_303_;
v_res_303_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_294_, v___y_295_);
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg___boxed(lean_object* v_mvarId_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec(v_mvarId_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12___redArg(lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
lean_object* v_ks_312_; lean_object* v_vs_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_337_; 
v_ks_312_ = lean_ctor_get(v_x_308_, 0);
v_vs_313_ = lean_ctor_get(v_x_308_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_337_ == 0)
{
v___x_315_ = v_x_308_;
v_isShared_316_ = v_isSharedCheck_337_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_vs_313_);
lean_inc(v_ks_312_);
lean_dec(v_x_308_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_337_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_array_get_size(v_ks_312_);
v___x_318_ = lean_nat_dec_lt(v_x_309_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
lean_dec(v_x_309_);
v___x_319_ = lean_array_push(v_ks_312_, v_x_310_);
v___x_320_ = lean_array_push(v_vs_313_, v_x_311_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v___x_320_);
lean_ctor_set(v___x_315_, 0, v___x_319_);
v___x_322_ = v___x_315_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_319_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
else
{
lean_object* v_k_x27_324_; uint8_t v___x_325_; 
v_k_x27_324_ = lean_array_fget_borrowed(v_ks_312_, v_x_309_);
v___x_325_ = l_Lean_instBEqMVarId_beq(v_x_310_, v_k_x27_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_327_; 
if (v_isShared_316_ == 0)
{
v___x_327_ = v___x_315_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_ks_312_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_vs_313_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(1u);
v___x_329_ = lean_nat_add(v_x_309_, v___x_328_);
lean_dec(v_x_309_);
v_x_308_ = v___x_327_;
v_x_309_ = v___x_329_;
goto _start;
}
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_332_ = lean_array_fset(v_ks_312_, v_x_309_, v_x_310_);
v___x_333_ = lean_array_fset(v_vs_313_, v_x_309_, v_x_311_);
lean_dec(v_x_309_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v___x_333_);
lean_ctor_set(v___x_315_, 0, v___x_332_);
v___x_335_ = v___x_315_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11___redArg(lean_object* v_n_338_, lean_object* v_k_339_, lean_object* v_v_340_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12___redArg(v_n_338_, v___x_341_, v_k_339_, v_v_340_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_343_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(lean_object* v_x_344_, size_t v_x_345_, size_t v_x_346_, lean_object* v_x_347_, lean_object* v_x_348_){
_start:
{
if (lean_obj_tag(v_x_344_) == 0)
{
lean_object* v_es_349_; size_t v___x_350_; size_t v___x_351_; lean_object* v_j_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_es_349_ = lean_ctor_get(v_x_344_, 0);
v___x_350_ = ((size_t)31ULL);
v___x_351_ = lean_usize_land(v_x_345_, v___x_350_);
v_j_352_ = lean_usize_to_nat(v___x_351_);
v___x_353_ = lean_array_get_size(v_es_349_);
v___x_354_ = lean_nat_dec_lt(v_j_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_dec(v_j_352_);
lean_dec(v_x_348_);
lean_dec(v_x_347_);
return v_x_344_;
}
else
{
lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_393_; 
lean_inc_ref(v_es_349_);
v_isSharedCheck_393_ = !lean_is_exclusive(v_x_344_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; 
v_unused_394_ = lean_ctor_get(v_x_344_, 0);
lean_dec(v_unused_394_);
v___x_356_ = v_x_344_;
v_isShared_357_ = v_isSharedCheck_393_;
goto v_resetjp_355_;
}
else
{
lean_dec(v_x_344_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_393_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v_v_358_; lean_object* v___x_359_; lean_object* v_xs_x27_360_; lean_object* v___y_362_; 
v_v_358_ = lean_array_fget(v_es_349_, v_j_352_);
v___x_359_ = lean_box(0);
v_xs_x27_360_ = lean_array_fset(v_es_349_, v_j_352_, v___x_359_);
switch(lean_obj_tag(v_v_358_))
{
case 0:
{
lean_object* v_key_367_; lean_object* v_val_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_378_; 
v_key_367_ = lean_ctor_get(v_v_358_, 0);
v_val_368_ = lean_ctor_get(v_v_358_, 1);
v_isSharedCheck_378_ = !lean_is_exclusive(v_v_358_);
if (v_isSharedCheck_378_ == 0)
{
v___x_370_ = v_v_358_;
v_isShared_371_ = v_isSharedCheck_378_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_val_368_);
lean_inc(v_key_367_);
lean_dec(v_v_358_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_378_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
uint8_t v___x_372_; 
v___x_372_ = l_Lean_instBEqMVarId_beq(v_x_347_, v_key_367_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_del_object(v___x_370_);
v___x_373_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_367_, v_val_368_, v_x_347_, v_x_348_);
v___x_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
v___y_362_ = v___x_374_;
goto v___jp_361_;
}
else
{
lean_object* v___x_376_; 
lean_dec(v_val_368_);
lean_dec(v_key_367_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 1, v_x_348_);
lean_ctor_set(v___x_370_, 0, v_x_347_);
v___x_376_ = v___x_370_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_x_347_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_x_348_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v___y_362_ = v___x_376_;
goto v___jp_361_;
}
}
}
}
case 1:
{
lean_object* v_node_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_391_; 
v_node_379_ = lean_ctor_get(v_v_358_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v_v_358_);
if (v_isSharedCheck_391_ == 0)
{
v___x_381_ = v_v_358_;
v_isShared_382_ = v_isSharedCheck_391_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_node_379_);
lean_dec(v_v_358_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_391_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
size_t v___x_383_; size_t v___x_384_; size_t v___x_385_; size_t v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_383_ = ((size_t)5ULL);
v___x_384_ = lean_usize_shift_right(v_x_345_, v___x_383_);
v___x_385_ = ((size_t)1ULL);
v___x_386_ = lean_usize_add(v_x_346_, v___x_385_);
v___x_387_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_node_379_, v___x_384_, v___x_386_, v_x_347_, v_x_348_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_387_);
v___x_389_ = v___x_381_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
v___y_362_ = v___x_389_;
goto v___jp_361_;
}
}
}
default: 
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_392_, 0, v_x_347_);
lean_ctor_set(v___x_392_, 1, v_x_348_);
v___y_362_ = v___x_392_;
goto v___jp_361_;
}
}
v___jp_361_:
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_array_fset(v_xs_x27_360_, v_j_352_, v___y_362_);
lean_dec(v_j_352_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 0, v___x_363_);
v___x_365_ = v___x_356_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
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
}
else
{
lean_object* v_ks_395_; lean_object* v_vs_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_414_; 
v_ks_395_ = lean_ctor_get(v_x_344_, 0);
v_vs_396_ = lean_ctor_get(v_x_344_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_344_);
if (v_isSharedCheck_414_ == 0)
{
v___x_398_ = v_x_344_;
v_isShared_399_ = v_isSharedCheck_414_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_vs_396_);
lean_inc(v_ks_395_);
lean_dec(v_x_344_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_414_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_ks_395_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_vs_396_);
v___x_401_ = v_reuseFailAlloc_413_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v_newNode_402_; size_t v___x_403_; uint8_t v___x_404_; 
v_newNode_402_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11___redArg(v___x_401_, v_x_347_, v_x_348_);
v___x_403_ = ((size_t)7ULL);
v___x_404_ = lean_usize_dec_le(v___x_403_, v_x_346_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_405_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_402_);
v___x_406_ = lean_unsigned_to_nat(4u);
v___x_407_ = lean_nat_dec_lt(v___x_405_, v___x_406_);
lean_dec(v___x_405_);
if (v___x_407_ == 0)
{
lean_object* v_ks_408_; lean_object* v_vs_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_ks_408_ = lean_ctor_get(v_newNode_402_, 0);
lean_inc_ref(v_ks_408_);
v_vs_409_ = lean_ctor_get(v_newNode_402_, 1);
lean_inc_ref(v_vs_409_);
lean_dec_ref(v_newNode_402_);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0);
v___x_412_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_x_346_, v_ks_408_, v_vs_409_, v___x_410_, v___x_411_);
lean_dec_ref(v_vs_409_);
lean_dec_ref(v_ks_408_);
return v___x_412_;
}
else
{
return v_newNode_402_;
}
}
else
{
return v_newNode_402_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_344_ = stack[0].m_obj;
size_t v_x_345_ = stack[1].m_num;
size_t v_x_346_ = stack[2].m_num;
lean_object* v_x_347_ = stack[3].m_obj;
lean_object* v_x_348_ = stack[4].m_obj;
lean_object* v_res_415_;
v_res_415_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_344_, v_x_345_, v_x_346_, v_x_347_, v_x_348_);
stack->m_obj
 = v_res_415_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(size_t v_depth_416_, lean_object* v_keys_417_, lean_object* v_vals_418_, lean_object* v_i_419_, lean_object* v_entries_420_){
_start:
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = lean_array_get_size(v_keys_417_);
v___x_422_ = lean_nat_dec_lt(v_i_419_, v___x_421_);
if (v___x_422_ == 0)
{
lean_dec(v_i_419_);
return v_entries_420_;
}
else
{
lean_object* v_k_423_; lean_object* v_v_424_; uint64_t v___x_425_; size_t v_h_426_; size_t v___x_427_; lean_object* v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; size_t v_h_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_k_423_ = lean_array_fget_borrowed(v_keys_417_, v_i_419_);
v_v_424_ = lean_array_fget_borrowed(v_vals_418_, v_i_419_);
v___x_425_ = l_Lean_instHashableMVarId_hash(v_k_423_);
v_h_426_ = lean_uint64_to_usize(v___x_425_);
v___x_427_ = ((size_t)5ULL);
v___x_428_ = lean_unsigned_to_nat(1u);
v___x_429_ = ((size_t)1ULL);
v___x_430_ = lean_usize_sub(v_depth_416_, v___x_429_);
v___x_431_ = lean_usize_mul(v___x_427_, v___x_430_);
v_h_432_ = lean_usize_shift_right(v_h_426_, v___x_431_);
v___x_433_ = lean_nat_add(v_i_419_, v___x_428_);
lean_dec(v_i_419_);
lean_inc(v_v_424_);
lean_inc(v_k_423_);
v___x_434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_entries_420_, v_h_432_, v_depth_416_, v_k_423_, v_v_424_);
v_i_419_ = v___x_433_;
v_entries_420_ = v___x_434_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_416_ = stack[0].m_num;
lean_object* v_keys_417_ = stack[1].m_obj;
lean_object* v_vals_418_ = stack[2].m_obj;
lean_object* v_i_419_ = stack[3].m_obj;
lean_object* v_entries_420_ = stack[4].m_obj;
lean_object* v_res_436_;
v_res_436_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_depth_416_, v_keys_417_, v_vals_418_, v_i_419_, v_entries_420_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_depth_437_, lean_object* v_keys_438_, lean_object* v_vals_439_, lean_object* v_i_440_, lean_object* v_entries_441_){
_start:
{
size_t v_depth_boxed_442_; lean_object* v_res_443_; 
v_depth_boxed_442_ = lean_unbox_usize(v_depth_437_);
lean_dec(v_depth_437_);
v_res_443_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_depth_boxed_442_, v_keys_438_, v_vals_439_, v_i_440_, v_entries_441_);
lean_dec_ref(v_vals_439_);
lean_dec_ref(v_keys_438_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
size_t v_x_44289__boxed_449_; size_t v_x_44290__boxed_450_; lean_object* v_res_451_; 
v_x_44289__boxed_449_ = lean_unbox_usize(v_x_445_);
lean_dec(v_x_445_);
v_x_44290__boxed_450_ = lean_unbox_usize(v_x_446_);
lean_dec(v_x_446_);
v_res_451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_444_, v_x_44289__boxed_449_, v_x_44290__boxed_450_, v_x_447_, v_x_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
uint64_t v___x_455_; size_t v___x_456_; size_t v___x_457_; lean_object* v___x_458_; 
v___x_455_ = l_Lean_instHashableMVarId_hash(v_x_453_);
v___x_456_ = lean_uint64_to_usize(v___x_455_);
v___x_457_ = ((size_t)1ULL);
v___x_458_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_452_, v___x_456_, v___x_457_, v_x_453_, v_x_454_);
return v___x_458_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(lean_object* v_mvarId_459_, lean_object* v_val_460_, lean_object* v___y_461_){
_start:
{
lean_object* v___x_463_; lean_object* v_mctx_464_; lean_object* v_cache_465_; lean_object* v_zetaDeltaFVarIds_466_; lean_object* v_postponed_467_; lean_object* v_diag_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_498_; 
v___x_463_ = lean_st_ref_take(v___y_461_);
v_mctx_464_ = lean_ctor_get(v___x_463_, 0);
v_cache_465_ = lean_ctor_get(v___x_463_, 1);
v_zetaDeltaFVarIds_466_ = lean_ctor_get(v___x_463_, 2);
v_postponed_467_ = lean_ctor_get(v___x_463_, 3);
v_diag_468_ = lean_ctor_get(v___x_463_, 4);
v_isSharedCheck_498_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_498_ == 0)
{
v___x_470_ = v___x_463_;
v_isShared_471_ = v_isSharedCheck_498_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_diag_468_);
lean_inc(v_postponed_467_);
lean_inc(v_zetaDeltaFVarIds_466_);
lean_inc(v_cache_465_);
lean_inc(v_mctx_464_);
lean_dec(v___x_463_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_498_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v_depth_472_; lean_object* v_levelAssignDepth_473_; lean_object* v_lmvarCounter_474_; lean_object* v_mvarCounter_475_; lean_object* v_lDecls_476_; lean_object* v_decls_477_; lean_object* v_userNames_478_; lean_object* v_lAssignment_479_; lean_object* v_eAssignment_480_; lean_object* v_dAssignment_481_; lean_object* v_instanceTypedMVars_482_; lean_object* v_synthNormMemo_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_497_; 
v_depth_472_ = lean_ctor_get(v_mctx_464_, 0);
v_levelAssignDepth_473_ = lean_ctor_get(v_mctx_464_, 1);
v_lmvarCounter_474_ = lean_ctor_get(v_mctx_464_, 2);
v_mvarCounter_475_ = lean_ctor_get(v_mctx_464_, 3);
v_lDecls_476_ = lean_ctor_get(v_mctx_464_, 4);
v_decls_477_ = lean_ctor_get(v_mctx_464_, 5);
v_userNames_478_ = lean_ctor_get(v_mctx_464_, 6);
v_lAssignment_479_ = lean_ctor_get(v_mctx_464_, 7);
v_eAssignment_480_ = lean_ctor_get(v_mctx_464_, 8);
v_dAssignment_481_ = lean_ctor_get(v_mctx_464_, 9);
v_instanceTypedMVars_482_ = lean_ctor_get(v_mctx_464_, 10);
v_synthNormMemo_483_ = lean_ctor_get(v_mctx_464_, 11);
v_isSharedCheck_497_ = !lean_is_exclusive(v_mctx_464_);
if (v_isSharedCheck_497_ == 0)
{
v___x_485_ = v_mctx_464_;
v_isShared_486_ = v_isSharedCheck_497_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_synthNormMemo_483_);
lean_inc(v_instanceTypedMVars_482_);
lean_inc(v_dAssignment_481_);
lean_inc(v_eAssignment_480_);
lean_inc(v_lAssignment_479_);
lean_inc(v_userNames_478_);
lean_inc(v_decls_477_);
lean_inc(v_lDecls_476_);
lean_inc(v_mvarCounter_475_);
lean_inc(v_lmvarCounter_474_);
lean_inc(v_levelAssignDepth_473_);
lean_inc(v_depth_472_);
lean_dec(v_mctx_464_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_497_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v___x_487_ = lean_box(0);
v___x_488_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_eAssignment_480_, v_mvarId_459_, v_val_460_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 8, v___x_488_);
v___x_490_ = v___x_485_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_depth_472_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_levelAssignDepth_473_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_lmvarCounter_474_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_mvarCounter_475_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_lDecls_476_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v_decls_477_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_userNames_478_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_lAssignment_479_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_496_, 9, v_dAssignment_481_);
lean_ctor_set(v_reuseFailAlloc_496_, 10, v_instanceTypedMVars_482_);
lean_ctor_set(v_reuseFailAlloc_496_, 11, v_synthNormMemo_483_);
v___x_490_ = v_reuseFailAlloc_496_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_object* v___x_492_; 
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_490_);
v___x_492_ = v___x_470_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_cache_465_);
lean_ctor_set(v_reuseFailAlloc_495_, 2, v_zetaDeltaFVarIds_466_);
lean_ctor_set(v_reuseFailAlloc_495_, 3, v_postponed_467_);
lean_ctor_set(v_reuseFailAlloc_495_, 4, v_diag_468_);
v___x_492_ = v_reuseFailAlloc_495_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_st_ref_put(v___y_461_, v___x_492_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_487_);
return v___x_494_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_459_ = stack[0].m_obj;
lean_object* v_val_460_ = stack[1].m_obj;
lean_object* v___y_461_ = stack[2].m_obj;
lean_object* v_res_499_;
v_res_499_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_459_, v_val_460_, v___y_461_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(lean_object* v_mvarId_500_, lean_object* v_val_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_500_, v_val_501_, v___y_502_);
lean_dec(v___y_502_);
return v_res_504_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(lean_object* v_mvarId_505_, lean_object* v_fst_506_, lean_object* v_a_507_, uint8_t v___y_508_, lean_object* v___x_509_, lean_object* v_val_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; 
lean_inc_ref(v_val_510_);
v___x_521_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_505_, v_val_510_, v___y_517_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_533_; 
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v___x_521_, 0);
lean_dec(v_unused_534_);
v___x_523_ = v___x_521_;
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
else
{
lean_dec(v___x_521_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_533_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_525_ = lean_array_fset(v_fst_506_, v_a_507_, v_val_510_);
v___x_526_ = lean_box(v___y_508_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_509_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_529_);
v___x_531_ = v___x_523_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec_ref(v_val_510_);
lean_dec(v___x_509_);
lean_dec(v_fst_506_);
v_a_535_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_521_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_521_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_505_ = stack[0].m_obj;
lean_object* v_fst_506_ = stack[1].m_obj;
lean_object* v_a_507_ = stack[2].m_obj;
uint8_t v___y_508_ = stack[3].m_num;
lean_object* v___x_509_ = stack[4].m_obj;
lean_object* v_val_510_ = stack[5].m_obj;
lean_object* v___y_511_ = stack[6].m_obj;
lean_object* v___y_512_ = stack[7].m_obj;
lean_object* v___y_513_ = stack[8].m_obj;
lean_object* v___y_514_ = stack[9].m_obj;
lean_object* v___y_515_ = stack[10].m_obj;
lean_object* v___y_516_ = stack[11].m_obj;
lean_object* v___y_517_ = stack[12].m_obj;
lean_object* v___y_518_ = stack[13].m_obj;
lean_object* v___y_519_ = stack[14].m_obj;
lean_object* v_res_543_;
v_res_543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_505_, v_fst_506_, v_a_507_, v___y_508_, v___x_509_, v_val_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
stack->m_obj
 = v_res_543_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed(lean_object* v_mvarId_544_, lean_object* v_fst_545_, lean_object* v_a_546_, lean_object* v___y_547_, lean_object* v___x_548_, lean_object* v_val_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
uint8_t v___y_44613__boxed_560_; lean_object* v_res_561_; 
v___y_44613__boxed_560_ = lean_unbox(v___y_547_);
v_res_561_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_544_, v_fst_545_, v_a_546_, v___y_44613__boxed_560_, v___x_548_, v_val_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec(v_a_546_);
return v_res_561_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(lean_object* v_upperBound_562_, lean_object* v_mvarCounterSaved_563_, lean_object* v_d_564_, lean_object* v_thm_565_, lean_object* v_a_566_, lean_object* v_b_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_a_579_; lean_object* v___y_584_; uint8_t v___x_603_; 
v___x_603_ = lean_nat_dec_lt(v_a_566_, v_upperBound_562_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v_b_567_);
return v___x_604_;
}
else
{
lean_object* v_snd_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_758_; 
v_snd_605_ = lean_ctor_get(v_b_567_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_b_567_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v_b_567_, 0);
lean_dec(v_unused_759_);
v___x_607_ = v_b_567_;
v_isShared_608_ = v_isSharedCheck_758_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_snd_605_);
lean_dec(v_b_567_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_758_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_fst_609_; lean_object* v_snd_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_757_; 
v_fst_609_ = lean_ctor_get(v_snd_605_, 0);
v_snd_610_ = lean_ctor_get(v_snd_605_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_snd_605_);
if (v_isSharedCheck_757_ == 0)
{
v___x_612_ = v_snd_605_;
v_isShared_613_ = v_isSharedCheck_757_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_snd_610_);
lean_inc(v_fst_609_);
lean_dec(v_snd_605_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_757_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_box(0);
v___x_615_ = lean_array_fget_borrowed(v_fst_609_, v_a_566_);
if (lean_obj_tag(v___x_615_) == 2)
{
lean_object* v_mvarId_616_; lean_object* v___x_617_; 
v_mvarId_616_ = lean_ctor_get(v___x_615_, 0);
v___x_617_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_616_, v___y_574_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; uint8_t v___x_619_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_617_, 1);
v___x_619_ = lean_unbox(v_a_618_);
lean_dec(v_a_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_inc(v_mvarId_616_);
v___x_620_ = l_Lean_MVarId_getDecl(v_mvarId_616_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_a_621_; lean_object* v_type_622_; lean_object* v_index_623_; uint8_t v___x_624_; 
v_a_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_a_621_);
lean_dec_ref_known(v___x_620_, 1);
v_type_622_ = lean_ctor_get(v_a_621_, 2);
lean_inc_ref(v_type_622_);
v_index_623_ = lean_ctor_get(v_a_621_, 6);
lean_inc(v_index_623_);
lean_dec(v_a_621_);
v___x_624_ = lean_nat_dec_le(v_mvarCounterSaved_563_, v_index_623_);
lean_dec(v_index_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_626_; 
lean_dec_ref(v_type_622_);
if (v_isShared_613_ == 0)
{
v___x_626_ = v___x_612_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_fst_609_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_snd_610_);
v___x_626_ = v_reuseFailAlloc_630_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_628_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_626_);
lean_ctor_set(v___x_607_, 0, v___x_614_);
v___x_628_ = v___x_607_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
v_a_579_ = v___x_628_;
goto v___jp_578_;
}
}
}
else
{
lean_object* v___x_631_; 
lean_inc_ref(v_d_564_);
lean_inc(v___y_576_);
lean_inc_ref(v___y_575_);
lean_inc(v___y_574_);
lean_inc_ref(v___y_573_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
lean_inc(v___y_568_);
v___x_631_ = lean_apply_11(v_d_564_, v_type_622_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, lean_box(0));
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_691_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_691_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_691_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_691_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
uint8_t v___y_637_; 
if (lean_obj_tag(v_a_632_) == 0)
{
uint8_t v___x_650_; 
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v___x_650_ = lean_unbox(v_snd_610_);
lean_dec(v_snd_610_);
if (v___x_650_ == 0)
{
uint8_t v_contextDependent_651_; 
v_contextDependent_651_ = lean_ctor_get_uint8(v_a_632_, 0);
lean_dec_ref_known(v_a_632_, 0);
v___y_637_ = v_contextDependent_651_;
goto v___jp_636_;
}
else
{
lean_dec_ref_known(v_a_632_, 0);
v___y_637_ = v___x_603_;
goto v___jp_636_;
}
}
else
{
lean_object* v_proof_652_; uint8_t v_contextDependent_653_; uint8_t v___y_655_; uint8_t v___x_690_; 
lean_inc(v_mvarId_616_);
lean_del_object(v___x_634_);
lean_del_object(v___x_612_);
lean_del_object(v___x_607_);
v_proof_652_ = lean_ctor_get(v_a_632_, 0);
lean_inc_ref(v_proof_652_);
v_contextDependent_653_ = lean_ctor_get_uint8(v_a_632_, sizeof(void*)*1);
lean_dec_ref_known(v_a_632_, 1);
v___x_690_ = lean_unbox(v_snd_610_);
lean_dec(v_snd_610_);
if (v___x_690_ == 0)
{
v___y_655_ = v_contextDependent_653_;
goto v___jp_654_;
}
else
{
v___y_655_ = v___x_603_;
goto v___jp_654_;
}
v___jp_654_:
{
lean_object* v_rhsVarMask_656_; uint8_t v___x_657_; 
v_rhsVarMask_656_ = lean_ctor_get(v_thm_565_, 3);
v___x_657_ = l_Nat_testBit(v_rhsVarMask_656_, v_a_566_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_proof_652_, v___y_574_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v___x_660_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_616_, v_fst_609_, v_a_566_, v___y_655_, v___x_614_, v_a_659_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
v___y_584_ = v___x_660_;
goto v___jp_583_;
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v_mvarId_616_);
lean_dec(v_fst_609_);
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v_a_661_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_658_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_658_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_proof_652_, v___y_574_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_671_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref_known(v___x_669_, 1);
v___x_671_ = l_Lean_Meta_Sym_shareCommon(v_a_670_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_616_, v_fst_609_, v_a_566_, v___y_655_, v___x_614_, v_a_672_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
v___y_584_ = v___x_673_;
goto v___jp_583_;
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_mvarId_616_);
lean_dec(v_fst_609_);
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v_a_674_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_671_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_671_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_mvarId_616_);
lean_dec(v_fst_609_);
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v_a_682_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_669_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_669_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
}
v___jp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_638_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_637_);
v___x_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
v___x_640_ = lean_box(v___y_637_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v___x_640_);
v___x_642_ = v___x_612_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_fst_609_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v___x_640_);
v___x_642_ = v_reuseFailAlloc_649_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_644_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_642_);
lean_ctor_set(v___x_607_, 0, v___x_639_);
v___x_644_ = v___x_607_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_639_);
lean_ctor_set(v_reuseFailAlloc_648_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_648_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_646_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_644_);
v___x_646_ = v___x_634_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_del_object(v___x_612_);
lean_dec(v_snd_610_);
lean_dec(v_fst_609_);
lean_del_object(v___x_607_);
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v_a_692_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_631_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_631_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_del_object(v___x_612_);
lean_dec(v_snd_610_);
lean_dec(v_fst_609_);
lean_del_object(v___x_607_);
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v_a_700_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_620_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_620_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
else
{
lean_object* v___x_708_; 
lean_inc_ref(v___x_615_);
v___x_708_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_615_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = lean_array_fset(v_fst_609_, v_a_566_, v_a_709_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_710_);
v___x_712_ = v___x_612_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_716_, 1, v_snd_610_);
v___x_712_ = v_reuseFailAlloc_716_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_714_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_712_);
lean_ctor_set(v___x_607_, 0, v___x_614_);
v___x_714_ = v___x_607_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
v_a_579_ = v___x_714_;
goto v___jp_578_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_del_object(v___x_612_);
lean_dec(v_snd_610_);
lean_dec(v_fst_609_);
lean_del_object(v___x_607_);
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v_a_717_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_708_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_708_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_del_object(v___x_612_);
lean_dec(v_snd_610_);
lean_dec(v_fst_609_);
lean_del_object(v___x_607_);
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v_a_725_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_617_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_617_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
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
uint8_t v___x_733_; 
v___x_733_ = l_Lean_Expr_hasMVar(v___x_615_);
if (v___x_733_ == 0)
{
lean_object* v___x_735_; 
if (v_isShared_613_ == 0)
{
v___x_735_ = v___x_612_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_fst_609_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_snd_610_);
v___x_735_ = v_reuseFailAlloc_739_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_737_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_735_);
lean_ctor_set(v___x_607_, 0, v___x_614_);
v___x_737_ = v___x_607_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v___x_735_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
v_a_579_ = v___x_737_;
goto v___jp_578_;
}
}
}
else
{
lean_object* v___x_740_; 
lean_inc(v___x_615_);
v___x_740_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_615_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref_known(v___x_740_, 1);
v___x_742_ = lean_array_fset(v_fst_609_, v_a_566_, v_a_741_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_742_);
v___x_744_ = v___x_612_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_742_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_snd_610_);
v___x_744_ = v_reuseFailAlloc_748_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_746_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_744_);
lean_ctor_set(v___x_607_, 0, v___x_614_);
v___x_746_ = v___x_607_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_614_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
v_a_579_ = v___x_746_;
goto v___jp_578_;
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_del_object(v___x_612_);
lean_dec(v_snd_610_);
lean_dec(v_fst_609_);
lean_del_object(v___x_607_);
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v_a_749_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_740_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_740_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
}
}
v___jp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_add(v_a_566_, v___x_580_);
lean_dec(v_a_566_);
v_a_566_ = v___x_581_;
v_b_567_ = v_a_579_;
goto _start;
}
v___jp_583_:
{
if (lean_obj_tag(v___y_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_594_; 
v_a_585_ = lean_ctor_get(v___y_584_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___y_584_);
if (v_isSharedCheck_594_ == 0)
{
v___x_587_ = v___y_584_;
v_isShared_588_ = v_isSharedCheck_594_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___y_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_594_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
if (lean_obj_tag(v_a_585_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_591_; 
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v_a_589_ = lean_ctor_get(v_a_585_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v_a_585_, 1);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 0, v_a_589_);
v___x_591_ = v___x_587_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
else
{
lean_object* v_a_593_; 
lean_del_object(v___x_587_);
v_a_593_ = lean_ctor_get(v_a_585_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v_a_585_, 1);
v_a_579_ = v_a_593_;
goto v___jp_578_;
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec(v_a_566_);
lean_dec_ref(v_d_564_);
v_a_595_ = lean_ctor_get(v___y_584_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___y_584_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___y_584_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___y_584_);
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
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_562_ = stack[0].m_obj;
lean_object* v_mvarCounterSaved_563_ = stack[1].m_obj;
lean_object* v_d_564_ = stack[2].m_obj;
lean_object* v_thm_565_ = stack[3].m_obj;
lean_object* v_a_566_ = stack[4].m_obj;
lean_object* v_b_567_ = stack[5].m_obj;
lean_object* v___y_568_ = stack[6].m_obj;
lean_object* v___y_569_ = stack[7].m_obj;
lean_object* v___y_570_ = stack[8].m_obj;
lean_object* v___y_571_ = stack[9].m_obj;
lean_object* v___y_572_ = stack[10].m_obj;
lean_object* v___y_573_ = stack[11].m_obj;
lean_object* v___y_574_ = stack[12].m_obj;
lean_object* v___y_575_ = stack[13].m_obj;
lean_object* v___y_576_ = stack[14].m_obj;
lean_object* v_res_760_;
v_res_760_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_upperBound_562_, v_mvarCounterSaved_563_, v_d_564_, v_thm_565_, v_a_566_, v_b_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
stack->m_obj
 = v_res_760_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___boxed(lean_object* v_upperBound_761_, lean_object* v_mvarCounterSaved_762_, lean_object* v_d_763_, lean_object* v_thm_764_, lean_object* v_a_765_, lean_object* v_b_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_upperBound_761_, v_mvarCounterSaved_762_, v_d_763_, v_thm_764_, v_a_765_, v_b_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v_thm_764_);
lean_dec(v_mvarCounterSaved_762_);
lean_dec(v_upperBound_761_);
return v_res_777_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = l_List_reverse___redArg(v_x_779_);
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
return v___x_791_;
}
else
{
lean_object* v_head_792_; lean_object* v_tail_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_803_; 
v_head_792_ = lean_ctor_get(v_x_778_, 0);
v_tail_793_ = lean_ctor_get(v_x_778_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_x_778_);
if (v_isSharedCheck_803_ == 0)
{
v___x_795_ = v_x_778_;
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_tail_793_);
lean_inc(v_head_792_);
lean_dec(v_x_778_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_803_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v_a_798_; lean_object* v___x_800_; 
v___x_797_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_head_792_, v___y_786_);
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_797_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v_x_779_);
lean_ctor_set(v___x_795_, 0, v_a_798_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_798_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_x_779_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v_x_778_ = v_tail_793_;
v_x_779_ = v___x_800_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_778_ = stack[0].m_obj;
lean_object* v_x_779_ = stack[1].m_obj;
lean_object* v___y_780_ = stack[2].m_obj;
lean_object* v___y_781_ = stack[3].m_obj;
lean_object* v___y_782_ = stack[4].m_obj;
lean_object* v___y_783_ = stack[5].m_obj;
lean_object* v___y_784_ = stack[6].m_obj;
lean_object* v___y_785_ = stack[7].m_obj;
lean_object* v___y_786_ = stack[8].m_obj;
lean_object* v___y_787_ = stack[9].m_obj;
lean_object* v___y_788_ = stack[10].m_obj;
lean_object* v_res_804_;
v_res_804_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_x_778_, v_x_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
stack->m_obj
 = v_res_804_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1___boxed(lean_object* v_x_805_, lean_object* v_x_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_x_805_, v_x_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_);
lean_dec(v___y_815_);
lean_dec_ref(v___y_814_);
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
return v_res_817_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object* v_thm_820_, lean_object* v_e_821_, lean_object* v_d_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; lean_object* v_mctx_834_; lean_object* v_mvarCounter_835_; lean_object* v_expr_836_; lean_object* v_pattern_837_; lean_object* v_rhs_838_; uint8_t v_perm_839_; uint8_t v___x_840_; lean_object* v___x_841_; 
v___x_833_ = lean_st_ref_get(v___y_829_);
v_mctx_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc_ref(v_mctx_834_);
lean_dec(v___x_833_);
v_mvarCounter_835_ = lean_ctor_get(v_mctx_834_, 3);
lean_inc(v_mvarCounter_835_);
lean_dec_ref(v_mctx_834_);
v_expr_836_ = lean_ctor_get(v_thm_820_, 0);
lean_inc_ref(v_expr_836_);
v_pattern_837_ = lean_ctor_get(v_thm_820_, 1);
lean_inc_ref_n(v_pattern_837_, 2);
v_rhs_838_ = lean_ctor_get(v_thm_820_, 2);
lean_inc_ref(v_rhs_838_);
v_perm_839_ = lean_ctor_get_uint8(v_thm_820_, sizeof(void*)*4);
v___x_840_ = 1;
lean_inc_ref(v_e_821_);
v___x_841_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_837_, v_e_821_, v___x_840_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_953_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_953_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_953_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_953_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
if (lean_obj_tag(v_a_842_) == 1)
{
lean_object* v_val_846_; lean_object* v_us_847_; lean_object* v_args_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_del_object(v___x_844_);
v_val_846_ = lean_ctor_get(v_a_842_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v_a_842_, 1);
v_us_847_ = lean_ctor_get(v_val_846_, 0);
lean_inc(v_us_847_);
v_args_848_ = lean_ctor_get(v_val_846_, 1);
lean_inc_ref(v_args_848_);
lean_dec(v_val_846_);
v___x_849_ = lean_array_get_size(v_args_848_);
v___x_850_ = lean_box(0);
v___x_851_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_us_847_, v___x_850_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = 0;
v___x_855_ = lean_box(0);
v___x_856_ = lean_box(v___x_854_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v_args_848_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_855_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v___x_849_, v_mvarCounter_835_, v_d_822_, v_thm_820_, v___x_853_, v___x_858_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec_ref(v_thm_820_);
lean_dec(v_mvarCounter_835_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_932_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_932_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_932_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_932_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_fst_864_; 
v_fst_864_ = lean_ctor_get(v_a_860_, 0);
if (lean_obj_tag(v_fst_864_) == 0)
{
lean_object* v_snd_865_; lean_object* v_fst_866_; lean_object* v_snd_867_; lean_object* v_levelParams_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_del_object(v___x_862_);
v_snd_865_ = lean_ctor_get(v_a_860_, 1);
lean_inc(v_snd_865_);
lean_dec(v_a_860_);
v_fst_866_ = lean_ctor_get(v_snd_865_, 0);
lean_inc(v_fst_866_);
v_snd_867_ = lean_ctor_get(v_snd_865_, 1);
lean_inc(v_snd_867_);
lean_dec(v_snd_865_);
v_levelParams_868_ = lean_ctor_get(v_pattern_837_, 0);
lean_inc(v_levelParams_868_);
lean_inc(v_a_852_);
v___x_869_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(v_expr_836_, v_pattern_837_, v_a_852_, v_fst_866_);
v___x_870_ = l_Lean_Expr_instantiateLevelParams(v_rhs_838_, v_levelParams_868_, v_a_852_);
lean_dec_ref(v_rhs_838_);
v___x_871_ = l_Lean_Meta_Sym_shareCommonInc(v___x_870_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
v___x_873_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_a_872_, v_fst_866_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_911_; 
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_911_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_911_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_911_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
size_t v___x_878_; size_t v___x_879_; uint8_t v___x_880_; 
v___x_878_ = lean_ptr_addr(v_e_821_);
v___x_879_ = lean_ptr_addr(v_a_874_);
v___x_880_ = lean_usize_dec_eq(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_del_object(v___x_876_);
lean_inc(v_a_874_);
v___x_881_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_839_, v_e_821_, v_a_874_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_897_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_897_ == 0)
{
v___x_884_ = v___x_881_;
v_isShared_885_ = v_isSharedCheck_897_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_881_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_897_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
uint8_t v___x_886_; 
v___x_886_ = lean_unbox(v_a_882_);
lean_dec(v_a_882_);
if (v___x_886_ == 0)
{
uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
lean_dec(v_a_874_);
lean_dec_ref(v___x_869_);
v___x_887_ = lean_unbox(v_snd_867_);
lean_dec(v_snd_867_);
v___x_888_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_887_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_888_);
v___x_890_ = v___x_884_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
else
{
lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_895_; 
v___x_892_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_892_, 0, v_a_874_);
lean_ctor_set(v___x_892_, 1, v___x_869_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2, v___x_854_);
v___x_893_ = lean_unbox(v_snd_867_);
lean_dec(v_snd_867_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2 + 1, v___x_893_);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 0, v___x_892_);
v___x_895_ = v___x_884_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_892_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec(v_a_874_);
lean_dec_ref(v___x_869_);
lean_dec(v_snd_867_);
v_a_898_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_881_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_881_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
lean_dec(v_a_874_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v_e_821_);
v___x_906_ = lean_unbox(v_snd_867_);
lean_dec(v_snd_867_);
v___x_907_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_906_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_907_);
v___x_909_ = v___x_876_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec_ref(v___x_869_);
lean_dec(v_snd_867_);
lean_dec_ref(v_e_821_);
v_a_912_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_873_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_873_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec_ref(v___x_869_);
lean_dec(v_snd_867_);
lean_dec(v_fst_866_);
lean_dec_ref(v_e_821_);
v_a_920_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_871_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_871_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_val_928_; lean_object* v___x_930_; 
lean_inc_ref(v_fst_864_);
lean_dec(v_a_860_);
lean_dec(v_a_852_);
lean_dec_ref(v_rhs_838_);
lean_dec_ref(v_pattern_837_);
lean_dec_ref(v_expr_836_);
lean_dec_ref(v_e_821_);
v_val_928_ = lean_ctor_get(v_fst_864_, 0);
lean_inc(v_val_928_);
lean_dec_ref_known(v_fst_864_, 1);
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 0, v_val_928_);
v___x_930_ = v___x_862_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_val_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_a_852_);
lean_dec_ref(v_rhs_838_);
lean_dec_ref(v_pattern_837_);
lean_dec_ref(v_expr_836_);
lean_dec_ref(v_e_821_);
v_a_933_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_859_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_859_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec_ref(v_args_848_);
lean_dec_ref(v_rhs_838_);
lean_dec_ref(v_pattern_837_);
lean_dec_ref(v_expr_836_);
lean_dec(v_mvarCounter_835_);
lean_dec_ref(v_d_822_);
lean_dec_ref(v_e_821_);
lean_dec_ref(v_thm_820_);
v_a_941_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_851_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_851_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
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
else
{
lean_object* v___x_949_; lean_object* v___x_951_; 
lean_dec(v_a_842_);
lean_dec_ref(v_rhs_838_);
lean_dec_ref(v_pattern_837_);
lean_dec_ref(v_expr_836_);
lean_dec(v_mvarCounter_835_);
lean_dec_ref(v_d_822_);
lean_dec_ref(v_e_821_);
lean_dec_ref(v_thm_820_);
v___x_949_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0));
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_949_);
v___x_951_ = v___x_844_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
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
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v_rhs_838_);
lean_dec_ref(v_pattern_837_);
lean_dec_ref(v_expr_836_);
lean_dec(v_mvarCounter_835_);
lean_dec_ref(v_d_822_);
lean_dec_ref(v_e_821_);
lean_dec_ref(v_thm_820_);
v_a_954_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_841_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_841_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
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
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_820_ = stack[0].m_obj;
lean_object* v_e_821_ = stack[1].m_obj;
lean_object* v_d_822_ = stack[2].m_obj;
lean_object* v___y_823_ = stack[3].m_obj;
lean_object* v___y_824_ = stack[4].m_obj;
lean_object* v___y_825_ = stack[5].m_obj;
lean_object* v___y_826_ = stack[6].m_obj;
lean_object* v___y_827_ = stack[7].m_obj;
lean_object* v___y_828_ = stack[8].m_obj;
lean_object* v___y_829_ = stack[9].m_obj;
lean_object* v___y_830_ = stack[10].m_obj;
lean_object* v___y_831_ = stack[11].m_obj;
lean_object* v_res_962_;
v_res_962_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(v_thm_820_, v_e_821_, v_d_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
stack->m_obj
 = v_res_962_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object* v_thm_963_, lean_object* v_e_964_, lean_object* v_d_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(v_thm_963_, v_e_964_, v_d_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
return v_res_976_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object* v_thm_977_, lean_object* v_e_978_, lean_object* v_d_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___f_990_; uint8_t v___x_991_; lean_object* v___x_992_; 
v___f_990_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed), 13, 3);
lean_closure_set(v___f_990_, 0, v_thm_977_);
lean_closure_set(v___f_990_, 1, v_e_978_);
lean_closure_set(v___f_990_, 2, v_d_979_);
v___x_991_ = 0;
v___x_992_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(v___f_990_, v___x_991_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
return v___x_992_;
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_Theorem_rewrite_0interp(lean_interpreter_value* stack)
{
lean_object* v_thm_977_ = stack[0].m_obj;
lean_object* v_e_978_ = stack[1].m_obj;
lean_object* v_d_979_ = stack[2].m_obj;
lean_object* v_a_980_ = stack[3].m_obj;
lean_object* v_a_981_ = stack[4].m_obj;
lean_object* v_a_982_ = stack[5].m_obj;
lean_object* v_a_983_ = stack[6].m_obj;
lean_object* v_a_984_ = stack[7].m_obj;
lean_object* v_a_985_ = stack[8].m_obj;
lean_object* v_a_986_ = stack[9].m_obj;
lean_object* v_a_987_ = stack[10].m_obj;
lean_object* v_a_988_ = stack[11].m_obj;
lean_object* v_res_993_;
v_res_993_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_thm_977_, v_e_978_, v_d_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_);
stack->m_obj
 = v_res_993_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object* v_thm_994_, lean_object* v_e_995_, lean_object* v_d_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_thm_994_, v_e_995_, v_d_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
return v_res_1007_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(lean_object* v_mvarId_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_1008_, v___y_1015_);
return v___x_1019_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1008_ = stack[0].m_obj;
lean_object* v___y_1009_ = stack[1].m_obj;
lean_object* v___y_1010_ = stack[2].m_obj;
lean_object* v___y_1011_ = stack[3].m_obj;
lean_object* v___y_1012_ = stack[4].m_obj;
lean_object* v___y_1013_ = stack[5].m_obj;
lean_object* v___y_1014_ = stack[6].m_obj;
lean_object* v___y_1015_ = stack[7].m_obj;
lean_object* v___y_1016_ = stack[8].m_obj;
lean_object* v___y_1017_ = stack[9].m_obj;
lean_object* v_res_1020_;
v_res_1020_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(v_mvarId_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
stack->m_obj
 = v_res_1020_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(lean_object* v_mvarId_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(v_mvarId_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec(v_mvarId_1021_);
return v_res_1032_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(lean_object* v_mvarId_1033_, lean_object* v_val_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_1033_, v_val_1034_, v___y_1041_);
return v___x_1045_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1033_ = stack[0].m_obj;
lean_object* v_val_1034_ = stack[1].m_obj;
lean_object* v___y_1035_ = stack[2].m_obj;
lean_object* v___y_1036_ = stack[3].m_obj;
lean_object* v___y_1037_ = stack[4].m_obj;
lean_object* v___y_1038_ = stack[5].m_obj;
lean_object* v___y_1039_ = stack[6].m_obj;
lean_object* v___y_1040_ = stack[7].m_obj;
lean_object* v___y_1041_ = stack[8].m_obj;
lean_object* v___y_1042_ = stack[9].m_obj;
lean_object* v___y_1043_ = stack[10].m_obj;
lean_object* v_res_1046_;
v_res_1046_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(v_mvarId_1033_, v_val_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
stack->m_obj
 = v_res_1046_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(lean_object* v_mvarId_1047_, lean_object* v_val_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(v_mvarId_1047_, v_val_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
return v_res_1059_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(lean_object* v_upperBound_1060_, lean_object* v_mvarCounterSaved_1061_, lean_object* v_d_1062_, lean_object* v___x_1063_, lean_object* v_thm_1064_, lean_object* v_inst_1065_, lean_object* v_R_1066_, lean_object* v_a_1067_, lean_object* v_b_1068_, lean_object* v_c_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_upperBound_1060_, v_mvarCounterSaved_1061_, v_d_1062_, v_thm_1064_, v_a_1067_, v_b_1068_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_1060_ = stack[0].m_obj;
lean_object* v_mvarCounterSaved_1061_ = stack[1].m_obj;
lean_object* v_d_1062_ = stack[2].m_obj;
lean_object* v___x_1063_ = stack[3].m_obj;
lean_object* v_thm_1064_ = stack[4].m_obj;
lean_object* v_a_1067_ = stack[7].m_obj;
lean_object* v_b_1068_ = stack[8].m_obj;
lean_object* v___y_1070_ = stack[10].m_obj;
lean_object* v___y_1071_ = stack[11].m_obj;
lean_object* v___y_1072_ = stack[12].m_obj;
lean_object* v___y_1073_ = stack[13].m_obj;
lean_object* v___y_1074_ = stack[14].m_obj;
lean_object* v___y_1075_ = stack[15].m_obj;
lean_object* v___y_1076_ = stack[16].m_obj;
lean_object* v___y_1077_ = stack[17].m_obj;
lean_object* v___y_1078_ = stack[18].m_obj;
lean_object* v_res_1081_;
v_res_1081_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(v_upperBound_1060_, v_mvarCounterSaved_1061_, v_d_1062_, v___x_1063_, v_thm_1064_, lean_box(0), lean_box(0), v_a_1067_, v_b_1068_, lean_box(0), v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
stack->m_obj
 = v_res_1081_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_1082_ = _args[0];
lean_object* v_mvarCounterSaved_1083_ = _args[1];
lean_object* v_d_1084_ = _args[2];
lean_object* v___x_1085_ = _args[3];
lean_object* v_thm_1086_ = _args[4];
lean_object* v_inst_1087_ = _args[5];
lean_object* v_R_1088_ = _args[6];
lean_object* v_a_1089_ = _args[7];
lean_object* v_b_1090_ = _args[8];
lean_object* v_c_1091_ = _args[9];
lean_object* v___y_1092_ = _args[10];
lean_object* v___y_1093_ = _args[11];
lean_object* v___y_1094_ = _args[12];
lean_object* v___y_1095_ = _args[13];
lean_object* v___y_1096_ = _args[14];
lean_object* v___y_1097_ = _args[15];
lean_object* v___y_1098_ = _args[16];
lean_object* v___y_1099_ = _args[17];
lean_object* v___y_1100_ = _args[18];
lean_object* v___y_1101_ = _args[19];
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(v_upperBound_1082_, v_mvarCounterSaved_1083_, v_d_1084_, v___x_1085_, v_thm_1086_, v_inst_1087_, v_R_1088_, v_a_1089_, v_b_1090_, v_c_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v_thm_1086_);
lean_dec(v___x_1085_);
lean_dec(v_mvarCounterSaved_1083_);
lean_dec(v_upperBound_1082_);
return v_res_1102_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_object* v_00_u03b2_1103_, lean_object* v_x_1104_, lean_object* v_x_1105_){
_start:
{
uint8_t v___x_1106_; 
v___x_1106_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_1104_, v_x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1104_ = stack[1].m_obj;
lean_object* v_x_1105_ = stack[2].m_obj;
uint8_t v_res_1107_;
v_res_1107_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_box(0), v_x_1104_, v_x_1105_);
stack->m_num = v_res_1107_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(v_00_u03b2_1108_, v_x_1109_, v_x_1110_);
lean_dec(v_x_1110_);
lean_dec_ref(v_x_1109_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(lean_object* v_00_u03b2_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_x_1114_, v_x_1115_, v_x_1116_);
return v___x_1117_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1118_, lean_object* v_x_1119_, size_t v_x_1120_, lean_object* v_x_1121_){
_start:
{
uint8_t v___x_1122_; 
v___x_1122_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_1119_, v_x_1120_, v_x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1119_ = stack[1].m_obj;
size_t v_x_1120_ = stack[2].m_num;
lean_object* v_x_1121_ = stack[3].m_obj;
uint8_t v_res_1123_;
v_res_1123_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(lean_box(0), v_x_1119_, v_x_1120_, v_x_1121_);
stack->m_num = v_res_1123_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_){
_start:
{
size_t v_x_46052__boxed_1128_; uint8_t v_res_1129_; lean_object* v_r_1130_; 
v_x_46052__boxed_1128_ = lean_unbox_usize(v_x_1126_);
lean_dec(v_x_1126_);
v_res_1129_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(v_00_u03b2_1124_, v_x_1125_, v_x_46052__boxed_1128_, v_x_1127_);
lean_dec(v_x_1127_);
lean_dec_ref(v_x_1125_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(lean_object* v_00_u03b2_1131_, lean_object* v_x_1132_, size_t v_x_1133_, size_t v_x_1134_, lean_object* v_x_1135_, lean_object* v_x_1136_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_1132_, v_x_1133_, v_x_1134_, v_x_1135_, v_x_1136_);
return v___x_1137_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1132_ = stack[1].m_obj;
size_t v_x_1133_ = stack[2].m_num;
size_t v_x_1134_ = stack[3].m_num;
lean_object* v_x_1135_ = stack[4].m_obj;
lean_object* v_x_1136_ = stack[5].m_obj;
lean_object* v_res_1138_;
v_res_1138_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(lean_box(0), v_x_1132_, v_x_1133_, v_x_1134_, v_x_1135_, v_x_1136_);
stack->m_obj
 = v_res_1138_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
size_t v_x_46070__boxed_1145_; size_t v_x_46071__boxed_1146_; lean_object* v_res_1147_; 
v_x_46070__boxed_1145_ = lean_unbox_usize(v_x_1141_);
lean_dec(v_x_1141_);
v_x_46071__boxed_1146_ = lean_unbox_usize(v_x_1142_);
lean_dec(v_x_1142_);
v_res_1147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(v_00_u03b2_1139_, v_x_1140_, v_x_46070__boxed_1145_, v_x_46071__boxed_1146_, v_x_1143_, v_x_1144_);
return v_res_1147_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1148_, lean_object* v_keys_1149_, lean_object* v_vals_1150_, lean_object* v_heq_1151_, lean_object* v_i_1152_, lean_object* v_k_1153_){
_start:
{
uint8_t v___x_1154_; 
v___x_1154_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_keys_1149_, v_i_1152_, v_k_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_1149_ = stack[1].m_obj;
lean_object* v_vals_1150_ = stack[2].m_obj;
lean_object* v_i_1152_ = stack[4].m_obj;
lean_object* v_k_1153_ = stack[5].m_obj;
uint8_t v_res_1155_;
v_res_1155_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(lean_box(0), v_keys_1149_, v_vals_1150_, lean_box(0), v_i_1152_, v_k_1153_);
stack->m_num = v_res_1155_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1156_, lean_object* v_keys_1157_, lean_object* v_vals_1158_, lean_object* v_heq_1159_, lean_object* v_i_1160_, lean_object* v_k_1161_){
_start:
{
uint8_t v_res_1162_; lean_object* v_r_1163_; 
v_res_1162_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(v_00_u03b2_1156_, v_keys_1157_, v_vals_1158_, v_heq_1159_, v_i_1160_, v_k_1161_);
lean_dec(v_k_1161_);
lean_dec_ref(v_vals_1158_);
lean_dec_ref(v_keys_1157_);
v_r_1163_ = lean_box(v_res_1162_);
return v_r_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_1164_, lean_object* v_n_1165_, lean_object* v_k_1166_, lean_object* v_v_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11___redArg(v_n_1165_, v_k_1166_, v_v_1167_);
return v___x_1168_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1169_, size_t v_depth_1170_, lean_object* v_keys_1171_, lean_object* v_vals_1172_, lean_object* v_heq_1173_, lean_object* v_i_1174_, lean_object* v_entries_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_depth_1170_, v_keys_1171_, v_vals_1172_, v_i_1174_, v_entries_1175_);
return v___x_1176_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1170_ = stack[1].m_num;
lean_object* v_keys_1171_ = stack[2].m_obj;
lean_object* v_vals_1172_ = stack[3].m_obj;
lean_object* v_i_1174_ = stack[5].m_obj;
lean_object* v_entries_1175_ = stack[6].m_obj;
lean_object* v_res_1177_;
v_res_1177_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(lean_box(0), v_depth_1170_, v_keys_1171_, v_vals_1172_, lean_box(0), v_i_1174_, v_entries_1175_);
stack->m_obj
 = v_res_1177_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1178_, lean_object* v_depth_1179_, lean_object* v_keys_1180_, lean_object* v_vals_1181_, lean_object* v_heq_1182_, lean_object* v_i_1183_, lean_object* v_entries_1184_){
_start:
{
size_t v_depth_boxed_1185_; lean_object* v_res_1186_; 
v_depth_boxed_1185_ = lean_unbox_usize(v_depth_1179_);
lean_dec(v_depth_1179_);
v_res_1186_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(v_00_u03b2_1178_, v_depth_boxed_1185_, v_keys_1180_, v_vals_1181_, v_heq_1182_, v_i_1183_, v_entries_1184_);
lean_dec_ref(v_vals_1181_);
lean_dec_ref(v_keys_1180_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1187_, lean_object* v_x_1188_, lean_object* v_x_1189_, lean_object* v_x_1190_, lean_object* v_x_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12___redArg(v_x_1188_, v_x_1189_, v_x_1190_, v_x_1191_);
return v___x_1192_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0(lean_object* v_fst_1193_, lean_object* v_d_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1193_, v_x_1195_, v_d_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
return v___x_1206_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1193_ = stack[0].m_obj;
lean_object* v_d_1194_ = stack[1].m_obj;
lean_object* v_x_1195_ = stack[2].m_obj;
lean_object* v___y_1196_ = stack[3].m_obj;
lean_object* v___y_1197_ = stack[4].m_obj;
lean_object* v___y_1198_ = stack[5].m_obj;
lean_object* v___y_1199_ = stack[6].m_obj;
lean_object* v___y_1200_ = stack[7].m_obj;
lean_object* v___y_1201_ = stack[8].m_obj;
lean_object* v___y_1202_ = stack[9].m_obj;
lean_object* v___y_1203_ = stack[10].m_obj;
lean_object* v___y_1204_ = stack[11].m_obj;
lean_object* v_res_1207_;
v_res_1207_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0(v_fst_1193_, v_d_1194_, v_x_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
stack->m_obj
 = v_res_1207_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0___boxed(lean_object* v_fst_1208_, lean_object* v_d_1209_, lean_object* v_x_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0(v_fst_1208_, v_d_1209_, v_x_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
return v_res_1221_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0(lean_object* v_d_1222_, lean_object* v_e_1223_, lean_object* v_as_1224_, size_t v_sz_1225_, size_t v_i_1226_, lean_object* v_b_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1248_; uint8_t v___y_1249_; lean_object* v___y_1252_; uint8_t v___y_1253_; uint8_t v___y_1254_; uint8_t v___y_1255_; lean_object* v___y_1257_; uint8_t v___y_1258_; uint8_t v___y_1259_; lean_object* v___y_1263_; uint8_t v___y_1264_; uint8_t v___x_1266_; 
v___x_1266_ = lean_usize_dec_lt(v_i_1226_, v_sz_1225_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1267_; 
lean_dec_ref(v_e_1223_);
lean_dec_ref(v_d_1222_);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v_b_1227_);
return v___x_1267_;
}
else
{
lean_object* v_a_1268_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v_snd_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1320_; 
v_a_1268_ = lean_array_uget_borrowed(v_as_1224_, v_i_1226_);
v_fst_1269_ = lean_ctor_get(v_a_1268_, 0);
v_snd_1270_ = lean_ctor_get(v_a_1268_, 1);
v_snd_1271_ = lean_ctor_get(v_b_1227_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_b_1227_);
if (v_isSharedCheck_1320_ == 0)
{
lean_object* v_unused_1321_; 
v_unused_1321_ = lean_ctor_get(v_b_1227_, 0);
lean_dec(v_unused_1321_);
v___x_1273_ = v_b_1227_;
v_isShared_1274_ = v_isSharedCheck_1320_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_snd_1271_);
lean_dec(v_b_1227_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1320_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___y_1277_; uint8_t v_done_1278_; uint8_t v___y_1279_; lean_object* v_result_1289_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1275_ = lean_box(0);
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = lean_nat_dec_eq(v_snd_1270_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___f_1299_; lean_object* v___x_1300_; 
lean_inc_ref(v_d_1222_);
lean_inc(v_fst_1269_);
v___f_1299_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1299_, 0, v_fst_1269_);
lean_closure_set(v___f_1299_, 1, v_d_1222_);
lean_inc_ref(v_e_1223_);
v___x_1300_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_1223_, v_snd_1270_, v___f_1299_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v_result_1289_ = v_a_1301_;
goto v___jp_1288_;
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_del_object(v___x_1273_);
lean_dec(v_snd_1271_);
lean_dec_ref(v_e_1223_);
lean_dec_ref(v_d_1222_);
v_a_1302_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1300_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1300_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
else
{
lean_object* v___x_1310_; 
lean_inc_ref(v_d_1222_);
lean_inc_ref(v_e_1223_);
lean_inc(v_fst_1269_);
v___x_1310_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1269_, v_e_1223_, v_d_1222_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
v_result_1289_ = v_a_1311_;
goto v___jp_1288_;
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_del_object(v___x_1273_);
lean_dec(v_snd_1271_);
lean_dec_ref(v_e_1223_);
lean_dec_ref(v_d_1222_);
v_a_1312_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1310_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1310_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
v___jp_1276_:
{
if (v_done_1278_ == 0)
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
lean_dec_ref(v___y_1277_);
v___x_1280_ = lean_box(v___y_1279_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v___x_1280_);
lean_ctor_set(v___x_1273_, 0, v___x_1275_);
v___x_1282_ = v___x_1273_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
size_t v___x_1283_; size_t v___x_1284_; 
v___x_1283_ = ((size_t)1ULL);
v___x_1284_ = lean_usize_add(v_i_1226_, v___x_1283_);
v_i_1226_ = v___x_1284_;
v_b_1227_ = v___x_1282_;
goto _start;
}
}
else
{
uint8_t v___x_1287_; 
lean_del_object(v___x_1273_);
lean_dec_ref(v_e_1223_);
lean_dec_ref(v_d_1222_);
v___x_1287_ = 0;
v___y_1257_ = v___y_1277_;
v___y_1258_ = v___y_1279_;
v___y_1259_ = v___x_1287_;
goto v___jp_1256_;
}
}
v___jp_1288_:
{
uint8_t v___x_1290_; 
v___x_1290_ = lean_unbox(v_snd_1271_);
if (v___x_1290_ == 0)
{
lean_dec(v_snd_1271_);
if (lean_obj_tag(v_result_1289_) == 0)
{
uint8_t v_done_1291_; uint8_t v_contextDependent_1292_; 
v_done_1291_ = lean_ctor_get_uint8(v_result_1289_, 0);
v_contextDependent_1292_ = lean_ctor_get_uint8(v_result_1289_, 1);
v___y_1277_ = v_result_1289_;
v_done_1278_ = v_done_1291_;
v___y_1279_ = v_contextDependent_1292_;
goto v___jp_1276_;
}
else
{
uint8_t v_contextDependent_1293_; 
lean_del_object(v___x_1273_);
lean_dec_ref(v_e_1223_);
lean_dec_ref(v_d_1222_);
v_contextDependent_1293_ = lean_ctor_get_uint8(v_result_1289_, sizeof(void*)*2 + 1);
v___y_1263_ = v_result_1289_;
v___y_1264_ = v_contextDependent_1293_;
goto v___jp_1262_;
}
}
else
{
if (lean_obj_tag(v_result_1289_) == 0)
{
uint8_t v_done_1294_; uint8_t v___x_1295_; 
v_done_1294_ = lean_ctor_get_uint8(v_result_1289_, 0);
v___x_1295_ = lean_unbox(v_snd_1271_);
lean_dec(v_snd_1271_);
v___y_1277_ = v_result_1289_;
v_done_1278_ = v_done_1294_;
v___y_1279_ = v___x_1295_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1296_; 
lean_del_object(v___x_1273_);
lean_dec_ref(v_e_1223_);
lean_dec_ref(v_d_1222_);
v___x_1296_ = lean_unbox(v_snd_1271_);
lean_dec(v_snd_1271_);
v___y_1263_ = v_result_1289_;
v___y_1264_ = v___x_1296_;
goto v___jp_1262_;
}
}
}
}
}
v___jp_1238_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1241_ = lean_box(v___y_1239_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___y_1240_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
v___x_1244_ = lean_box(v___y_1239_);
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1243_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
return v___x_1246_;
}
v___jp_1247_:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1248_);
v___y_1239_ = v___y_1249_;
v___y_1240_ = v___x_1250_;
goto v___jp_1238_;
}
v___jp_1251_:
{
if (v___y_1255_ == 0)
{
v___y_1248_ = v___y_1252_;
v___y_1249_ = v___y_1254_;
goto v___jp_1247_;
}
else
{
if (v___y_1253_ == 0)
{
v___y_1239_ = v___y_1254_;
v___y_1240_ = v___y_1252_;
goto v___jp_1238_;
}
else
{
v___y_1248_ = v___y_1252_;
v___y_1249_ = v___y_1254_;
goto v___jp_1247_;
}
}
}
v___jp_1256_:
{
if (v___y_1258_ == 0)
{
v___y_1239_ = v___y_1258_;
v___y_1240_ = v___y_1257_;
goto v___jp_1238_;
}
else
{
if (lean_obj_tag(v___y_1257_) == 0)
{
uint8_t v_contextDependent_1260_; 
v_contextDependent_1260_ = lean_ctor_get_uint8(v___y_1257_, 1);
v___y_1252_ = v___y_1257_;
v___y_1253_ = v___y_1259_;
v___y_1254_ = v___y_1258_;
v___y_1255_ = v_contextDependent_1260_;
goto v___jp_1251_;
}
else
{
uint8_t v_contextDependent_1261_; 
v_contextDependent_1261_ = lean_ctor_get_uint8(v___y_1257_, sizeof(void*)*2 + 1);
v___y_1252_ = v___y_1257_;
v___y_1253_ = v___y_1259_;
v___y_1254_ = v___y_1258_;
v___y_1255_ = v_contextDependent_1261_;
goto v___jp_1251_;
}
}
}
v___jp_1262_:
{
uint8_t v___x_1265_; 
v___x_1265_ = 0;
v___y_1257_ = v___y_1263_;
v___y_1258_ = v___y_1264_;
v___y_1259_ = v___x_1265_;
goto v___jp_1256_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_1222_ = stack[0].m_obj;
lean_object* v_e_1223_ = stack[1].m_obj;
lean_object* v_as_1224_ = stack[2].m_obj;
size_t v_sz_1225_ = stack[3].m_num;
size_t v_i_1226_ = stack[4].m_num;
lean_object* v_b_1227_ = stack[5].m_obj;
lean_object* v___y_1228_ = stack[6].m_obj;
lean_object* v___y_1229_ = stack[7].m_obj;
lean_object* v___y_1230_ = stack[8].m_obj;
lean_object* v___y_1231_ = stack[9].m_obj;
lean_object* v___y_1232_ = stack[10].m_obj;
lean_object* v___y_1233_ = stack[11].m_obj;
lean_object* v___y_1234_ = stack[12].m_obj;
lean_object* v___y_1235_ = stack[13].m_obj;
lean_object* v___y_1236_ = stack[14].m_obj;
lean_object* v_res_1322_;
v_res_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0(v_d_1222_, v_e_1223_, v_as_1224_, v_sz_1225_, v_i_1226_, v_b_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
stack->m_obj
 = v_res_1322_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___boxed(lean_object* v_d_1323_, lean_object* v_e_1324_, lean_object* v_as_1325_, lean_object* v_sz_1326_, lean_object* v_i_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
size_t v_sz_boxed_1339_; size_t v_i_boxed_1340_; lean_object* v_res_1341_; 
v_sz_boxed_1339_ = lean_unbox_usize(v_sz_1326_);
lean_dec(v_sz_1326_);
v_i_boxed_1340_ = lean_unbox_usize(v_i_1327_);
lean_dec(v_i_1327_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0(v_d_1323_, v_e_1324_, v_as_1325_, v_sz_boxed_1339_, v_i_boxed_1340_, v_b_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v_as_1325_);
return v_res_1341_;
}
}
lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing(lean_object* v_candidates_1342_, lean_object* v_e_1343_, lean_object* v_d_1344_, uint8_t v_anyCD_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; size_t v_sz_1359_; size_t v___x_1360_; lean_object* v___x_1361_; 
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_box(v_anyCD_1345_);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v_sz_1359_ = lean_array_size(v_candidates_1342_);
v___x_1360_ = ((size_t)0ULL);
v___x_1361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0(v_d_1344_, v_e_1343_, v_candidates_1342_, v_sz_1359_, v___x_1360_, v___x_1358_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1385_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1385_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1385_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v_fst_1366_; 
v_fst_1366_ = lean_ctor_get(v_a_1362_, 0);
if (lean_obj_tag(v_fst_1366_) == 0)
{
lean_object* v_snd_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1379_; 
v_snd_1367_ = lean_ctor_get(v_a_1362_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_a_1362_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v_a_1362_, 0);
lean_dec(v_unused_1380_);
v___x_1369_ = v_a_1362_;
v_isShared_1370_ = v_isSharedCheck_1379_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_snd_1367_);
lean_dec(v_a_1362_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1379_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1371_ = lean_unbox(v_snd_1367_);
v___x_1372_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1371_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1372_);
v___x_1374_ = v___x_1369_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_snd_1367_);
v___x_1374_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1376_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v___x_1374_);
v___x_1376_ = v___x_1364_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
else
{
lean_object* v_val_1381_; lean_object* v___x_1383_; 
lean_inc_ref(v_fst_1366_);
lean_dec(v_a_1362_);
v_val_1381_ = lean_ctor_get(v_fst_1366_, 0);
lean_inc(v_val_1381_);
lean_dec_ref_known(v_fst_1366_, 1);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 0, v_val_1381_);
v___x_1383_ = v___x_1364_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_val_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
v_a_1386_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1361_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1361_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1391_; 
if (v_isShared_1389_ == 0)
{
v___x_1391_ = v___x_1388_;
goto v_reusejp_1390_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
v___x_1391_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1390_;
}
v_reusejp_1390_:
{
return v___x_1391_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_0interp(lean_interpreter_value* stack)
{
lean_object* v_candidates_1342_ = stack[0].m_obj;
lean_object* v_e_1343_ = stack[1].m_obj;
lean_object* v_d_1344_ = stack[2].m_obj;
uint8_t v_anyCD_1345_ = stack[3].m_num;
lean_object* v_a_1346_ = stack[4].m_obj;
lean_object* v_a_1347_ = stack[5].m_obj;
lean_object* v_a_1348_ = stack[6].m_obj;
lean_object* v_a_1349_ = stack[7].m_obj;
lean_object* v_a_1350_ = stack[8].m_obj;
lean_object* v_a_1351_ = stack[9].m_obj;
lean_object* v_a_1352_ = stack[10].m_obj;
lean_object* v_a_1353_ = stack[11].m_obj;
lean_object* v_a_1354_ = stack[12].m_obj;
lean_object* v_res_1394_;
v_res_1394_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing(v_candidates_1342_, v_e_1343_, v_d_1344_, v_anyCD_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
stack->m_obj
 = v_res_1394_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing___boxed(lean_object* v_candidates_1395_, lean_object* v_e_1396_, lean_object* v_d_1397_, lean_object* v_anyCD_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_){
_start:
{
uint8_t v_anyCD_boxed_1409_; lean_object* v_res_1410_; 
v_anyCD_boxed_1409_ = lean_unbox(v_anyCD_1398_);
v_res_1410_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing(v_candidates_1395_, v_e_1396_, v_d_1397_, v_anyCD_boxed_1409_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
lean_dec(v_a_1405_);
lean_dec_ref(v_a_1404_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_candidates_1395_);
return v_res_1410_;
}
}
uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___redArg(lean_object* v_x_1411_){
_start:
{
uint8_t v___x_1412_; 
v___x_1412_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1411_ = stack[0].m_obj;
uint8_t v_res_1413_;
v_res_1413_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___redArg(v_x_1411_);
stack->m_num = v_res_1413_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___redArg___boxed(lean_object* v_x_1414_){
_start:
{
uint8_t v_res_1415_; lean_object* v_r_1416_; 
v_res_1415_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___redArg(v_x_1414_);
lean_dec_ref(v_x_1414_);
v_r_1416_ = lean_box(v_res_1415_);
return v_r_1416_;
}
}
uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object* v_00_u03b2_1417_, lean_object* v_x_1418_){
_start:
{
uint8_t v___x_1419_; 
v___x_1419_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1418_ = stack[1].m_obj;
uint8_t v_res_1420_;
v_res_1420_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_box(0), v_x_1418_);
stack->m_num = v_res_1420_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object* v_00_u03b2_1421_, lean_object* v_x_1422_){
_start:
{
uint8_t v_res_1423_; lean_object* v_r_1424_; 
v_res_1423_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_00_u03b2_1421_, v_x_1422_);
lean_dec_ref(v_x_1422_);
v_r_1424_ = lean_box(v_res_1423_);
return v_r_1424_;
}
}
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object* v_thms_1425_, lean_object* v_d_1426_, lean_object* v_e_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1438_; lean_object* v_mctx_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; lean_object* v___x_1442_; 
v___x_1438_ = lean_st_ref_get(v_a_1434_);
v_mctx_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_mctx_1439_);
lean_dec(v___x_1438_);
v___x_1440_ = l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(v_thms_1425_, v_mctx_1439_, v_e_1427_);
v___x_1441_ = 0;
lean_inc_ref(v_d_1426_);
lean_inc_ref(v_e_1427_);
v___x_1442_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing(v___x_1440_, v_e_1427_, v_d_1426_, v___x_1441_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
lean_dec_ref(v___x_1440_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1481_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1481_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1481_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v_fst_1447_; 
v_fst_1447_ = lean_ctor_get(v_a_1443_, 0);
lean_inc(v_fst_1447_);
if (lean_obj_tag(v_fst_1447_) == 0)
{
uint8_t v_done_1448_; 
v_done_1448_ = lean_ctor_get_uint8(v_fst_1447_, 0);
if (v_done_1448_ == 0)
{
lean_object* v_snd_1449_; lean_object* v_fallback_1450_; uint8_t v___x_1451_; 
v_snd_1449_ = lean_ctor_get(v_a_1443_, 1);
lean_inc(v_snd_1449_);
lean_dec(v_a_1443_);
v_fallback_1450_ = lean_ctor_get(v_thms_1425_, 1);
v___x_1451_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fallback_1450_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1452_; uint8_t v___x_1453_; lean_object* v___x_1454_; 
lean_dec_ref_known(v_fst_1447_, 0);
lean_del_object(v___x_1445_);
v___x_1452_ = l_Lean_Meta_Sym_Simp_Theorems_getFallbackMatchWithExtra(v_thms_1425_, v_mctx_1439_, v_e_1427_);
lean_dec_ref(v_mctx_1439_);
v___x_1453_ = lean_unbox(v_snd_1449_);
lean_dec(v_snd_1449_);
v___x_1454_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing(v___x_1452_, v_e_1427_, v_d_1426_, v___x_1453_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
lean_dec_ref(v___x_1452_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1463_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1463_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v_fst_1459_; lean_object* v___x_1461_; 
v_fst_1459_ = lean_ctor_get(v_a_1455_, 0);
lean_inc(v_fst_1459_);
lean_dec(v_a_1455_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 0, v_fst_1459_);
v___x_1461_ = v___x_1457_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_fst_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
v_a_1464_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1454_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1454_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v___x_1473_; 
lean_dec(v_snd_1449_);
lean_dec_ref(v_mctx_1439_);
lean_dec_ref(v_e_1427_);
lean_dec_ref(v_d_1426_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v_fst_1447_);
v___x_1473_ = v___x_1445_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_fst_1447_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
else
{
lean_object* v___x_1476_; 
lean_dec(v_a_1443_);
lean_dec_ref(v_mctx_1439_);
lean_dec_ref(v_e_1427_);
lean_dec_ref(v_d_1426_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v_fst_1447_);
v___x_1476_ = v___x_1445_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_fst_1447_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
else
{
lean_object* v___x_1479_; 
lean_dec(v_a_1443_);
lean_dec_ref(v_mctx_1439_);
lean_dec_ref(v_e_1427_);
lean_dec_ref(v_d_1426_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v_fst_1447_);
v___x_1479_ = v___x_1445_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_fst_1447_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v_mctx_1439_);
lean_dec_ref(v_e_1427_);
lean_dec_ref(v_d_1426_);
v_a_1482_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1442_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1442_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_Simp_Theorems_rewrite_0interp(lean_interpreter_value* stack)
{
lean_object* v_thms_1425_ = stack[0].m_obj;
lean_object* v_d_1426_ = stack[1].m_obj;
lean_object* v_e_1427_ = stack[2].m_obj;
lean_object* v_a_1428_ = stack[3].m_obj;
lean_object* v_a_1429_ = stack[4].m_obj;
lean_object* v_a_1430_ = stack[5].m_obj;
lean_object* v_a_1431_ = stack[6].m_obj;
lean_object* v_a_1432_ = stack[7].m_obj;
lean_object* v_a_1433_ = stack[8].m_obj;
lean_object* v_a_1434_ = stack[9].m_obj;
lean_object* v_a_1435_ = stack[10].m_obj;
lean_object* v_a_1436_ = stack[11].m_obj;
lean_object* v_res_1490_;
v_res_1490_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_thms_1425_, v_d_1426_, v_e_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_);
stack->m_obj
 = v_res_1490_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object* v_thms_1491_, lean_object* v_d_1492_, lean_object* v_e_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_thms_1491_, v_d_1492_, v_e_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_);
lean_dec(v_a_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_thms_1491_);
return v_res_1504_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
