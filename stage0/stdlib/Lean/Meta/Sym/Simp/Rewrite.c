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
v___x_7_ = l_Lean_Expr_instantiateLevelParams(v_expr_1_, v_levelParams_6_, v_us_3_);
lean_dec(v_us_3_);
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
lean_dec_ref(v_pattern_14_);
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
v___x_59_ = lean_st_ref_put(v___y_42_, v___x_58_);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(lean_object* v_e_92_, lean_object* v___y_93_){
_start:
{
uint8_t v___x_95_; 
v___x_95_ = l_Lean_Expr_hasMVar(v_e_92_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
v___x_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_96_, 0, v_e_92_);
return v___x_96_;
}
else
{
lean_object* v___x_97_; lean_object* v_mctx_98_; lean_object* v___x_99_; lean_object* v_fst_100_; lean_object* v_snd_101_; lean_object* v___x_102_; lean_object* v_cache_103_; lean_object* v_zetaDeltaFVarIds_104_; lean_object* v_postponed_105_; lean_object* v_diag_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_115_; 
v___x_97_ = lean_st_ref_get(v___y_93_);
v_mctx_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc_ref(v_mctx_98_);
lean_dec(v___x_97_);
v___x_99_ = l_Lean_instantiateMVarsCore(v_mctx_98_, v_e_92_);
v_fst_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_fst_100_);
v_snd_101_ = lean_ctor_get(v___x_99_, 1);
lean_inc(v_snd_101_);
lean_dec_ref(v___x_99_);
v___x_102_ = lean_st_ref_take(v___y_93_);
v_cache_103_ = lean_ctor_get(v___x_102_, 1);
v_zetaDeltaFVarIds_104_ = lean_ctor_get(v___x_102_, 2);
v_postponed_105_ = lean_ctor_get(v___x_102_, 3);
v_diag_106_ = lean_ctor_get(v___x_102_, 4);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_115_ == 0)
{
lean_object* v_unused_116_; 
v_unused_116_ = lean_ctor_get(v___x_102_, 0);
lean_dec(v_unused_116_);
v___x_108_ = v___x_102_;
v_isShared_109_ = v_isSharedCheck_115_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_diag_106_);
lean_inc(v_postponed_105_);
lean_inc(v_zetaDeltaFVarIds_104_);
lean_inc(v_cache_103_);
lean_dec(v___x_102_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_115_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v_snd_101_);
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_snd_101_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_cache_103_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_zetaDeltaFVarIds_104_);
lean_ctor_set(v_reuseFailAlloc_114_, 3, v_postponed_105_);
lean_ctor_set(v_reuseFailAlloc_114_, 4, v_diag_106_);
v___x_111_ = v_reuseFailAlloc_114_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_st_ref_put(v___y_93_, v___x_111_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v_fst_100_);
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg___boxed(lean_object* v_e_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_e_117_, v___y_118_);
lean_dec(v___y_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(lean_object* v_e_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_e_121_, v___y_128_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___boxed(lean_object* v_e_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4(v_e_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0(lean_object* v_k_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_){
_start:
{
lean_object* v___x_156_; 
lean_inc(v___y_150_);
lean_inc_ref(v___y_149_);
lean_inc(v___y_148_);
lean_inc_ref(v___y_147_);
lean_inc(v___y_146_);
v___x_156_ = lean_apply_10(v_k_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, lean_box(0));
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0___boxed(lean_object* v_k_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0(v_k_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(lean_object* v_k_169_, uint8_t v_allowLevelAssignments_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___f_181_; lean_object* v___x_182_; 
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
v___f_181_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___lam__0___boxed), 11, 6);
lean_closure_set(v___f_181_, 0, v_k_169_);
lean_closure_set(v___f_181_, 1, v___y_171_);
lean_closure_set(v___f_181_, 2, v___y_172_);
lean_closure_set(v___f_181_, 3, v___y_173_);
lean_closure_set(v___f_181_, 4, v___y_174_);
lean_closure_set(v___f_181_, 5, v___y_175_);
v___x_182_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_170_, v___f_181_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
if (lean_obj_tag(v___x_182_) == 0)
{
return v___x_182_;
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg___boxed(lean_object* v_k_191_, lean_object* v_allowLevelAssignments_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_203_; lean_object* v_res_204_; 
v_allowLevelAssignments_boxed_203_ = lean_unbox(v_allowLevelAssignments_192_);
v_res_204_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(v_k_191_, v_allowLevelAssignments_boxed_203_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6(lean_object* v_00_u03b1_205_, lean_object* v_k_206_, uint8_t v_allowLevelAssignments_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(v_k_206_, v_allowLevelAssignments_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___boxed(lean_object* v_00_u03b1_219_, lean_object* v_k_220_, lean_object* v_allowLevelAssignments_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_232_; lean_object* v_res_233_; 
v_allowLevelAssignments_boxed_232_ = lean_unbox(v_allowLevelAssignments_221_);
v_res_233_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6(v_00_u03b1_219_, v_k_220_, v_allowLevelAssignments_boxed_232_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
return v_res_233_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(lean_object* v_keys_234_, lean_object* v_i_235_, lean_object* v_k_236_){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = lean_array_get_size(v_keys_234_);
v___x_238_ = lean_nat_dec_lt(v_i_235_, v___x_237_);
if (v___x_238_ == 0)
{
lean_dec(v_i_235_);
return v___x_238_;
}
else
{
lean_object* v_k_x27_239_; uint8_t v___x_240_; 
v_k_x27_239_ = lean_array_fget_borrowed(v_keys_234_, v_i_235_);
v___x_240_ = l_Lean_instBEqMVarId_beq(v_k_236_, v_k_x27_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_add(v_i_235_, v___x_241_);
lean_dec(v_i_235_);
v_i_235_ = v___x_242_;
goto _start;
}
else
{
lean_dec(v_i_235_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_keys_244_, lean_object* v_i_245_, lean_object* v_k_246_){
_start:
{
uint8_t v_res_247_; lean_object* v_r_248_; 
v_res_247_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_keys_244_, v_i_245_, v_k_246_);
lean_dec(v_k_246_);
lean_dec_ref(v_keys_244_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(lean_object* v_x_249_, size_t v_x_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_object* v_es_252_; lean_object* v___x_253_; size_t v___x_254_; size_t v___x_255_; lean_object* v_j_256_; lean_object* v___x_257_; 
v_es_252_ = lean_ctor_get(v_x_249_, 0);
v___x_253_ = lean_box(2);
v___x_254_ = ((size_t)31ULL);
v___x_255_ = lean_usize_land(v_x_250_, v___x_254_);
v_j_256_ = lean_usize_to_nat(v___x_255_);
v___x_257_ = lean_array_get_borrowed(v___x_253_, v_es_252_, v_j_256_);
lean_dec(v_j_256_);
switch(lean_obj_tag(v___x_257_))
{
case 0:
{
lean_object* v_key_258_; uint8_t v___x_259_; 
v_key_258_ = lean_ctor_get(v___x_257_, 0);
v___x_259_ = l_Lean_instBEqMVarId_beq(v_x_251_, v_key_258_);
return v___x_259_;
}
case 1:
{
lean_object* v_node_260_; size_t v___x_261_; size_t v___x_262_; 
v_node_260_ = lean_ctor_get(v___x_257_, 0);
v___x_261_ = ((size_t)5ULL);
v___x_262_ = lean_usize_shift_right(v_x_250_, v___x_261_);
v_x_249_ = v_node_260_;
v_x_250_ = v___x_262_;
goto _start;
}
default: 
{
uint8_t v___x_264_; 
v___x_264_ = 0;
return v___x_264_;
}
}
}
else
{
lean_object* v_ks_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_ks_265_ = lean_ctor_get(v_x_249_, 0);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_ks_265_, v___x_266_, v_x_251_);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
size_t v_x_43907__boxed_271_; uint8_t v_res_272_; lean_object* v_r_273_; 
v_x_43907__boxed_271_ = lean_unbox_usize(v_x_269_);
lean_dec(v_x_269_);
v_res_272_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_268_, v_x_43907__boxed_271_, v_x_270_);
lean_dec(v_x_270_);
lean_dec_ref(v_x_268_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
uint64_t v___x_276_; size_t v___x_277_; uint8_t v___x_278_; 
v___x_276_ = l_Lean_instHashableMVarId_hash(v_x_275_);
v___x_277_ = lean_uint64_to_usize(v___x_276_);
v___x_278_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_274_, v___x_277_, v_x_275_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg___boxed(lean_object* v_x_279_, lean_object* v_x_280_){
_start:
{
uint8_t v_res_281_; lean_object* v_r_282_; 
v_res_281_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_279_, v_x_280_);
lean_dec(v_x_280_);
lean_dec_ref(v_x_279_);
v_r_282_ = lean_box(v_res_281_);
return v_r_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(lean_object* v_mvarId_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_286_; lean_object* v_mctx_287_; lean_object* v_eAssignment_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_286_ = lean_st_ref_get(v___y_284_);
v_mctx_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc_ref(v_mctx_287_);
lean_dec(v___x_286_);
v_eAssignment_288_ = lean_ctor_get(v_mctx_287_, 8);
lean_inc_ref(v_eAssignment_288_);
lean_dec_ref(v_mctx_287_);
v___x_289_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_eAssignment_288_, v_mvarId_283_);
lean_dec_ref(v_eAssignment_288_);
v___x_290_ = lean_box(v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg___boxed(lean_object* v_mvarId_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec(v_mvarId_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12___redArg(lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
lean_object* v_ks_300_; lean_object* v_vs_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_325_; 
v_ks_300_ = lean_ctor_get(v_x_296_, 0);
v_vs_301_ = lean_ctor_get(v_x_296_, 1);
v_isSharedCheck_325_ = !lean_is_exclusive(v_x_296_);
if (v_isSharedCheck_325_ == 0)
{
v___x_303_ = v_x_296_;
v_isShared_304_ = v_isSharedCheck_325_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_vs_301_);
lean_inc(v_ks_300_);
lean_dec(v_x_296_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_325_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = lean_array_get_size(v_ks_300_);
v___x_306_ = lean_nat_dec_lt(v_x_297_, v___x_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
lean_dec(v_x_297_);
v___x_307_ = lean_array_push(v_ks_300_, v_x_298_);
v___x_308_ = lean_array_push(v_vs_301_, v_x_299_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_308_);
lean_ctor_set(v___x_303_, 0, v___x_307_);
v___x_310_ = v___x_303_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_307_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v___x_308_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
else
{
lean_object* v_k_x27_312_; uint8_t v___x_313_; 
v_k_x27_312_ = lean_array_fget_borrowed(v_ks_300_, v_x_297_);
v___x_313_ = l_Lean_instBEqMVarId_beq(v_x_298_, v_k_x27_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_315_; 
if (v_isShared_304_ == 0)
{
v___x_315_ = v___x_303_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_ks_300_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_vs_301_);
v___x_315_ = v_reuseFailAlloc_319_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_add(v_x_297_, v___x_316_);
lean_dec(v_x_297_);
v_x_296_ = v___x_315_;
v_x_297_ = v___x_317_;
goto _start;
}
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_320_ = lean_array_fset(v_ks_300_, v_x_297_, v_x_298_);
v___x_321_ = lean_array_fset(v_vs_301_, v_x_297_, v_x_299_);
lean_dec(v_x_297_);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 1, v___x_321_);
lean_ctor_set(v___x_303_, 0, v___x_320_);
v___x_323_ = v___x_303_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11___redArg(lean_object* v_n_326_, lean_object* v_k_327_, lean_object* v_v_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12___redArg(v_n_326_, v___x_329_, v_k_327_, v_v_328_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(lean_object* v_x_332_, size_t v_x_333_, size_t v_x_334_, lean_object* v_x_335_, lean_object* v_x_336_){
_start:
{
if (lean_obj_tag(v_x_332_) == 0)
{
lean_object* v_es_337_; size_t v___x_338_; size_t v___x_339_; lean_object* v_j_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_es_337_ = lean_ctor_get(v_x_332_, 0);
v___x_338_ = ((size_t)31ULL);
v___x_339_ = lean_usize_land(v_x_333_, v___x_338_);
v_j_340_ = lean_usize_to_nat(v___x_339_);
v___x_341_ = lean_array_get_size(v_es_337_);
v___x_342_ = lean_nat_dec_lt(v_j_340_, v___x_341_);
if (v___x_342_ == 0)
{
lean_dec(v_j_340_);
lean_dec(v_x_336_);
lean_dec(v_x_335_);
return v_x_332_;
}
else
{
lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_381_; 
lean_inc_ref(v_es_337_);
v_isSharedCheck_381_ = !lean_is_exclusive(v_x_332_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; 
v_unused_382_ = lean_ctor_get(v_x_332_, 0);
lean_dec(v_unused_382_);
v___x_344_ = v_x_332_;
v_isShared_345_ = v_isSharedCheck_381_;
goto v_resetjp_343_;
}
else
{
lean_dec(v_x_332_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_381_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_v_346_; lean_object* v___x_347_; lean_object* v_xs_x27_348_; lean_object* v___y_350_; 
v_v_346_ = lean_array_fget(v_es_337_, v_j_340_);
v___x_347_ = lean_box(0);
v_xs_x27_348_ = lean_array_fset(v_es_337_, v_j_340_, v___x_347_);
switch(lean_obj_tag(v_v_346_))
{
case 0:
{
lean_object* v_key_355_; lean_object* v_val_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_366_; 
v_key_355_ = lean_ctor_get(v_v_346_, 0);
v_val_356_ = lean_ctor_get(v_v_346_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v_v_346_);
if (v_isSharedCheck_366_ == 0)
{
v___x_358_ = v_v_346_;
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_val_356_);
lean_inc(v_key_355_);
lean_dec(v_v_346_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_366_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
uint8_t v___x_360_; 
v___x_360_ = l_Lean_instBEqMVarId_beq(v_x_335_, v_key_355_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
lean_del_object(v___x_358_);
v___x_361_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_355_, v_val_356_, v_x_335_, v_x_336_);
v___x_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
v___y_350_ = v___x_362_;
goto v___jp_349_;
}
else
{
lean_object* v___x_364_; 
lean_dec(v_val_356_);
lean_dec(v_key_355_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 1, v_x_336_);
lean_ctor_set(v___x_358_, 0, v_x_335_);
v___x_364_ = v___x_358_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_x_335_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_x_336_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
v___y_350_ = v___x_364_;
goto v___jp_349_;
}
}
}
}
case 1:
{
lean_object* v_node_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_379_; 
v_node_367_ = lean_ctor_get(v_v_346_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v_v_346_);
if (v_isSharedCheck_379_ == 0)
{
v___x_369_ = v_v_346_;
v_isShared_370_ = v_isSharedCheck_379_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_node_367_);
lean_dec(v_v_346_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_379_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_371_ = ((size_t)5ULL);
v___x_372_ = lean_usize_shift_right(v_x_333_, v___x_371_);
v___x_373_ = ((size_t)1ULL);
v___x_374_ = lean_usize_add(v_x_334_, v___x_373_);
v___x_375_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_node_367_, v___x_372_, v___x_374_, v_x_335_, v_x_336_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_375_);
v___x_377_ = v___x_369_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
v___y_350_ = v___x_377_;
goto v___jp_349_;
}
}
}
default: 
{
lean_object* v___x_380_; 
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v_x_335_);
lean_ctor_set(v___x_380_, 1, v_x_336_);
v___y_350_ = v___x_380_;
goto v___jp_349_;
}
}
v___jp_349_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_array_fset(v_xs_x27_348_, v_j_340_, v___y_350_);
lean_dec(v_j_340_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 0, v___x_351_);
v___x_353_ = v___x_344_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
else
{
lean_object* v_ks_383_; lean_object* v_vs_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_402_; 
v_ks_383_ = lean_ctor_get(v_x_332_, 0);
v_vs_384_ = lean_ctor_get(v_x_332_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v_x_332_);
if (v_isSharedCheck_402_ == 0)
{
v___x_386_ = v_x_332_;
v_isShared_387_ = v_isSharedCheck_402_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_vs_384_);
lean_inc(v_ks_383_);
lean_dec(v_x_332_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_402_;
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
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_ks_383_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_vs_384_);
v___x_389_ = v_reuseFailAlloc_401_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v_newNode_390_; size_t v___x_391_; uint8_t v___x_392_; 
v_newNode_390_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11___redArg(v___x_389_, v_x_335_, v_x_336_);
v___x_391_ = ((size_t)7ULL);
v___x_392_ = lean_usize_dec_le(v___x_391_, v_x_334_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_393_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_390_);
v___x_394_ = lean_unsigned_to_nat(4u);
v___x_395_ = lean_nat_dec_lt(v___x_393_, v___x_394_);
lean_dec(v___x_393_);
if (v___x_395_ == 0)
{
lean_object* v_ks_396_; lean_object* v_vs_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v_ks_396_ = lean_ctor_get(v_newNode_390_, 0);
lean_inc_ref(v_ks_396_);
v_vs_397_ = lean_ctor_get(v_newNode_390_, 1);
lean_inc_ref(v_vs_397_);
lean_dec_ref(v_newNode_390_);
v___x_398_ = lean_unsigned_to_nat(0u);
v___x_399_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0);
v___x_400_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_x_334_, v_ks_396_, v_vs_397_, v___x_398_, v___x_399_);
lean_dec_ref(v_vs_397_);
lean_dec_ref(v_ks_396_);
return v___x_400_;
}
else
{
return v_newNode_390_;
}
}
else
{
return v_newNode_390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(size_t v_depth_403_, lean_object* v_keys_404_, lean_object* v_vals_405_, lean_object* v_i_406_, lean_object* v_entries_407_){
_start:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = lean_array_get_size(v_keys_404_);
v___x_409_ = lean_nat_dec_lt(v_i_406_, v___x_408_);
if (v___x_409_ == 0)
{
lean_dec(v_i_406_);
return v_entries_407_;
}
else
{
lean_object* v_k_410_; lean_object* v_v_411_; uint64_t v___x_412_; size_t v_h_413_; size_t v___x_414_; lean_object* v___x_415_; size_t v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v_h_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_k_410_ = lean_array_fget_borrowed(v_keys_404_, v_i_406_);
v_v_411_ = lean_array_fget_borrowed(v_vals_405_, v_i_406_);
v___x_412_ = l_Lean_instHashableMVarId_hash(v_k_410_);
v_h_413_ = lean_uint64_to_usize(v___x_412_);
v___x_414_ = ((size_t)5ULL);
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_sub(v_depth_403_, v___x_416_);
v___x_418_ = lean_usize_mul(v___x_414_, v___x_417_);
v_h_419_ = lean_usize_shift_right(v_h_413_, v___x_418_);
v___x_420_ = lean_nat_add(v_i_406_, v___x_415_);
lean_dec(v_i_406_);
lean_inc(v_v_411_);
lean_inc(v_k_410_);
v___x_421_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_entries_407_, v_h_419_, v_depth_403_, v_k_410_, v_v_411_);
v_i_406_ = v___x_420_;
v_entries_407_ = v___x_421_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_depth_423_, lean_object* v_keys_424_, lean_object* v_vals_425_, lean_object* v_i_426_, lean_object* v_entries_427_){
_start:
{
size_t v_depth_boxed_428_; lean_object* v_res_429_; 
v_depth_boxed_428_ = lean_unbox_usize(v_depth_423_);
lean_dec(v_depth_423_);
v_res_429_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_depth_boxed_428_, v_keys_424_, v_vals_425_, v_i_426_, v_entries_427_);
lean_dec_ref(v_vals_425_);
lean_dec_ref(v_keys_424_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
size_t v_x_44050__boxed_435_; size_t v_x_44051__boxed_436_; lean_object* v_res_437_; 
v_x_44050__boxed_435_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_x_44051__boxed_436_ = lean_unbox_usize(v_x_432_);
lean_dec(v_x_432_);
v_res_437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_430_, v_x_44050__boxed_435_, v_x_44051__boxed_436_, v_x_433_, v_x_434_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
uint64_t v___x_441_; size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_441_ = l_Lean_instHashableMVarId_hash(v_x_439_);
v___x_442_ = lean_uint64_to_usize(v___x_441_);
v___x_443_ = ((size_t)1ULL);
v___x_444_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_438_, v___x_442_, v___x_443_, v_x_439_, v_x_440_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(lean_object* v_mvarId_445_, lean_object* v_val_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; lean_object* v_mctx_450_; lean_object* v_cache_451_; lean_object* v_zetaDeltaFVarIds_452_; lean_object* v_postponed_453_; lean_object* v_diag_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_482_; 
v___x_449_ = lean_st_ref_take(v___y_447_);
v_mctx_450_ = lean_ctor_get(v___x_449_, 0);
v_cache_451_ = lean_ctor_get(v___x_449_, 1);
v_zetaDeltaFVarIds_452_ = lean_ctor_get(v___x_449_, 2);
v_postponed_453_ = lean_ctor_get(v___x_449_, 3);
v_diag_454_ = lean_ctor_get(v___x_449_, 4);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_482_ == 0)
{
v___x_456_ = v___x_449_;
v_isShared_457_ = v_isSharedCheck_482_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_diag_454_);
lean_inc(v_postponed_453_);
lean_inc(v_zetaDeltaFVarIds_452_);
lean_inc(v_cache_451_);
lean_inc(v_mctx_450_);
lean_dec(v___x_449_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_482_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_depth_458_; lean_object* v_levelAssignDepth_459_; lean_object* v_lmvarCounter_460_; lean_object* v_mvarCounter_461_; lean_object* v_lDecls_462_; lean_object* v_decls_463_; lean_object* v_userNames_464_; lean_object* v_lAssignment_465_; lean_object* v_eAssignment_466_; lean_object* v_dAssignment_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_481_; 
v_depth_458_ = lean_ctor_get(v_mctx_450_, 0);
v_levelAssignDepth_459_ = lean_ctor_get(v_mctx_450_, 1);
v_lmvarCounter_460_ = lean_ctor_get(v_mctx_450_, 2);
v_mvarCounter_461_ = lean_ctor_get(v_mctx_450_, 3);
v_lDecls_462_ = lean_ctor_get(v_mctx_450_, 4);
v_decls_463_ = lean_ctor_get(v_mctx_450_, 5);
v_userNames_464_ = lean_ctor_get(v_mctx_450_, 6);
v_lAssignment_465_ = lean_ctor_get(v_mctx_450_, 7);
v_eAssignment_466_ = lean_ctor_get(v_mctx_450_, 8);
v_dAssignment_467_ = lean_ctor_get(v_mctx_450_, 9);
v_isSharedCheck_481_ = !lean_is_exclusive(v_mctx_450_);
if (v_isSharedCheck_481_ == 0)
{
v___x_469_ = v_mctx_450_;
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_dAssignment_467_);
lean_inc(v_eAssignment_466_);
lean_inc(v_lAssignment_465_);
lean_inc(v_userNames_464_);
lean_inc(v_decls_463_);
lean_inc(v_lDecls_462_);
lean_inc(v_mvarCounter_461_);
lean_inc(v_lmvarCounter_460_);
lean_inc(v_levelAssignDepth_459_);
lean_inc(v_depth_458_);
lean_dec(v_mctx_450_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_481_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_471_ = lean_box(0);
v___x_472_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_eAssignment_466_, v_mvarId_445_, v_val_446_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 8, v___x_472_);
v___x_474_ = v___x_469_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_depth_458_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_levelAssignDepth_459_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_lmvarCounter_460_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_mvarCounter_461_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_lDecls_462_);
lean_ctor_set(v_reuseFailAlloc_480_, 5, v_decls_463_);
lean_ctor_set(v_reuseFailAlloc_480_, 6, v_userNames_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 7, v_lAssignment_465_);
lean_ctor_set(v_reuseFailAlloc_480_, 8, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_480_, 9, v_dAssignment_467_);
v___x_474_ = v_reuseFailAlloc_480_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_476_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_474_);
v___x_476_ = v___x_456_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v_cache_451_);
lean_ctor_set(v_reuseFailAlloc_479_, 2, v_zetaDeltaFVarIds_452_);
lean_ctor_set(v_reuseFailAlloc_479_, 3, v_postponed_453_);
lean_ctor_set(v_reuseFailAlloc_479_, 4, v_diag_454_);
v___x_476_ = v_reuseFailAlloc_479_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_st_ref_put(v___y_447_, v___x_476_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_471_);
return v___x_478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(lean_object* v_mvarId_483_, lean_object* v_val_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_483_, v_val_484_, v___y_485_);
lean_dec(v___y_485_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(lean_object* v_mvarId_488_, lean_object* v_fst_489_, lean_object* v_a_490_, uint8_t v___y_491_, lean_object* v___x_492_, lean_object* v_val_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; 
lean_inc_ref(v_val_493_);
v___x_504_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_488_, v_val_493_, v___y_500_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_516_; 
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v___x_504_, 0);
lean_dec(v_unused_517_);
v___x_506_ = v___x_504_;
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
else
{
lean_dec(v___x_504_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_516_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_508_ = lean_array_fset(v_fst_489_, v_a_490_, v_val_493_);
v___x_509_ = lean_box(v___y_491_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_492_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_512_);
v___x_514_ = v___x_506_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v___x_512_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_val_493_);
lean_dec(v___x_492_);
lean_dec(v_fst_489_);
v_a_518_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_504_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_504_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed(lean_object* v_mvarId_526_, lean_object* v_fst_527_, lean_object* v_a_528_, lean_object* v___y_529_, lean_object* v___x_530_, lean_object* v_val_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
uint8_t v___y_44260__boxed_542_; lean_object* v_res_543_; 
v___y_44260__boxed_542_ = lean_unbox(v___y_529_);
v_res_543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_526_, v_fst_527_, v_a_528_, v___y_44260__boxed_542_, v___x_530_, v_val_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec(v_a_528_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(lean_object* v_upperBound_544_, lean_object* v_mvarCounterSaved_545_, lean_object* v_d_546_, lean_object* v_thm_547_, lean_object* v_a_548_, lean_object* v_b_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_a_561_; lean_object* v___y_566_; uint8_t v___x_585_; 
v___x_585_ = lean_nat_dec_lt(v_a_548_, v_upperBound_544_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; 
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v___x_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_586_, 0, v_b_549_);
return v___x_586_;
}
else
{
lean_object* v_snd_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_740_; 
v_snd_587_ = lean_ctor_get(v_b_549_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_b_549_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_b_549_, 0);
lean_dec(v_unused_741_);
v___x_589_ = v_b_549_;
v_isShared_590_ = v_isSharedCheck_740_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_snd_587_);
lean_dec(v_b_549_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_740_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_739_; 
v_fst_591_ = lean_ctor_get(v_snd_587_, 0);
v_snd_592_ = lean_ctor_get(v_snd_587_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_snd_587_);
if (v_isSharedCheck_739_ == 0)
{
v___x_594_ = v_snd_587_;
v_isShared_595_ = v_isSharedCheck_739_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_snd_592_);
lean_inc(v_fst_591_);
lean_dec(v_snd_587_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_739_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_box(0);
v___x_597_ = lean_array_fget_borrowed(v_fst_591_, v_a_548_);
if (lean_obj_tag(v___x_597_) == 2)
{
lean_object* v_mvarId_598_; lean_object* v___x_599_; 
v_mvarId_598_ = lean_ctor_get(v___x_597_, 0);
v___x_599_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_598_, v___y_556_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; uint8_t v___x_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = lean_unbox(v_a_600_);
lean_dec(v_a_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_inc(v_mvarId_598_);
v___x_602_ = l_Lean_MVarId_getDecl(v_mvarId_598_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v_type_604_; lean_object* v_index_605_; uint8_t v___x_606_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v_type_604_ = lean_ctor_get(v_a_603_, 2);
lean_inc_ref(v_type_604_);
v_index_605_ = lean_ctor_get(v_a_603_, 6);
lean_inc(v_index_605_);
lean_dec(v_a_603_);
v___x_606_ = lean_nat_dec_le(v_mvarCounterSaved_545_, v_index_605_);
lean_dec(v_index_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_608_; 
lean_dec_ref(v_type_604_);
if (v_isShared_595_ == 0)
{
v___x_608_ = v___x_594_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_fst_591_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_snd_592_);
v___x_608_ = v_reuseFailAlloc_612_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_610_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v___x_608_);
lean_ctor_set(v___x_589_, 0, v___x_596_);
v___x_610_ = v___x_589_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
v_a_561_ = v___x_610_;
goto v___jp_560_;
}
}
}
else
{
lean_object* v___x_613_; 
lean_inc_ref(v_d_546_);
lean_inc(v___y_558_);
lean_inc_ref(v___y_557_);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
lean_inc_ref(v___y_551_);
lean_inc(v___y_550_);
v___x_613_ = lean_apply_11(v_d_546_, v_type_604_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, lean_box(0));
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_673_; 
v_a_614_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_673_ == 0)
{
v___x_616_ = v___x_613_;
v_isShared_617_ = v_isSharedCheck_673_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_613_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_673_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
uint8_t v___y_619_; 
if (lean_obj_tag(v_a_614_) == 0)
{
uint8_t v___x_632_; 
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v___x_632_ = lean_unbox(v_snd_592_);
lean_dec(v_snd_592_);
if (v___x_632_ == 0)
{
uint8_t v_contextDependent_633_; 
v_contextDependent_633_ = lean_ctor_get_uint8(v_a_614_, 0);
lean_dec_ref_known(v_a_614_, 0);
v___y_619_ = v_contextDependent_633_;
goto v___jp_618_;
}
else
{
lean_dec_ref_known(v_a_614_, 0);
v___y_619_ = v___x_585_;
goto v___jp_618_;
}
}
else
{
lean_object* v_proof_634_; uint8_t v_contextDependent_635_; uint8_t v___y_637_; uint8_t v___x_672_; 
lean_inc(v_mvarId_598_);
lean_del_object(v___x_616_);
lean_del_object(v___x_594_);
lean_del_object(v___x_589_);
v_proof_634_ = lean_ctor_get(v_a_614_, 0);
lean_inc_ref(v_proof_634_);
v_contextDependent_635_ = lean_ctor_get_uint8(v_a_614_, sizeof(void*)*1);
lean_dec_ref_known(v_a_614_, 1);
v___x_672_ = lean_unbox(v_snd_592_);
lean_dec(v_snd_592_);
if (v___x_672_ == 0)
{
v___y_637_ = v_contextDependent_635_;
goto v___jp_636_;
}
else
{
v___y_637_ = v___x_585_;
goto v___jp_636_;
}
v___jp_636_:
{
lean_object* v_rhsVarMask_638_; uint8_t v___x_639_; 
v_rhsVarMask_638_ = lean_ctor_get(v_thm_547_, 3);
v___x_639_ = l_Nat_testBit(v_rhsVarMask_638_, v_a_548_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_proof_634_, v___y_556_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_642_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_a_641_);
lean_dec_ref_known(v___x_640_, 1);
v___x_642_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_598_, v_fst_591_, v_a_548_, v___y_637_, v___x_596_, v_a_641_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
v___y_566_ = v___x_642_;
goto v___jp_565_;
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_mvarId_598_);
lean_dec(v_fst_591_);
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v_a_643_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_640_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_640_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_proof_634_, v___y_556_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; lean_object* v___x_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v___x_653_ = l_Lean_Meta_Sym_shareCommon(v_a_652_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_598_, v_fst_591_, v_a_548_, v___y_637_, v___x_596_, v_a_654_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
v___y_566_ = v___x_655_;
goto v___jp_565_;
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
lean_dec(v_mvarId_598_);
lean_dec(v_fst_591_);
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v_a_656_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_653_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_653_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
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
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v_mvarId_598_);
lean_dec(v_fst_591_);
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v_a_664_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_651_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_651_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
}
}
v___jp_618_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_620_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_619_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
v___x_622_ = lean_box(v___y_619_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v___x_622_);
v___x_624_ = v___x_594_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_fst_591_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_622_);
v___x_624_ = v_reuseFailAlloc_631_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_626_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v___x_624_);
lean_ctor_set(v___x_589_, 0, v___x_621_);
v___x_626_ = v___x_589_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v___x_624_);
v___x_626_ = v_reuseFailAlloc_630_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_628_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_626_);
v___x_628_ = v___x_616_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_del_object(v___x_594_);
lean_dec(v_snd_592_);
lean_dec(v_fst_591_);
lean_del_object(v___x_589_);
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v_a_674_ = lean_ctor_get(v___x_613_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_613_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_613_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_613_);
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
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_del_object(v___x_594_);
lean_dec(v_snd_592_);
lean_dec(v_fst_591_);
lean_del_object(v___x_589_);
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v_a_682_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_602_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_602_);
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
else
{
lean_object* v___x_690_; 
lean_inc_ref(v___x_597_);
v___x_690_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_597_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = lean_array_fset(v_fst_591_, v_a_548_, v_a_691_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_692_);
v___x_694_ = v___x_594_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_snd_592_);
v___x_694_ = v_reuseFailAlloc_698_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_696_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v___x_694_);
lean_ctor_set(v___x_589_, 0, v___x_596_);
v___x_696_ = v___x_589_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
v_a_561_ = v___x_696_;
goto v___jp_560_;
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_del_object(v___x_594_);
lean_dec(v_snd_592_);
lean_dec(v_fst_591_);
lean_del_object(v___x_589_);
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v_a_699_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_690_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_690_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_del_object(v___x_594_);
lean_dec(v_snd_592_);
lean_dec(v_fst_591_);
lean_del_object(v___x_589_);
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v_a_707_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_599_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_599_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
uint8_t v___x_715_; 
v___x_715_ = l_Lean_Expr_hasMVar(v___x_597_);
if (v___x_715_ == 0)
{
lean_object* v___x_717_; 
if (v_isShared_595_ == 0)
{
v___x_717_ = v___x_594_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_fst_591_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_snd_592_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v___x_717_);
lean_ctor_set(v___x_589_, 0, v___x_596_);
v___x_719_ = v___x_589_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
v_a_561_ = v___x_719_;
goto v___jp_560_;
}
}
}
else
{
lean_object* v___x_722_; 
lean_inc(v___x_597_);
v___x_722_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_597_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_722_, 1);
v___x_724_ = lean_array_fset(v_fst_591_, v_a_548_, v_a_723_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_724_);
v___x_726_ = v___x_594_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_snd_592_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v___x_726_);
lean_ctor_set(v___x_589_, 0, v___x_596_);
v___x_728_ = v___x_589_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
v_a_561_ = v___x_728_;
goto v___jp_560_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_del_object(v___x_594_);
lean_dec(v_snd_592_);
lean_dec(v_fst_591_);
lean_del_object(v___x_589_);
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v_a_731_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_722_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_722_);
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
}
}
}
v___jp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_a_548_, v___x_562_);
lean_dec(v_a_548_);
v_a_548_ = v___x_563_;
v_b_549_ = v_a_561_;
goto _start;
}
v___jp_565_:
{
if (lean_obj_tag(v___y_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_576_; 
v_a_567_ = lean_ctor_get(v___y_566_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___y_566_);
if (v_isSharedCheck_576_ == 0)
{
v___x_569_ = v___y_566_;
v_isShared_570_ = v_isSharedCheck_576_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___y_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_576_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
if (lean_obj_tag(v_a_567_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; 
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v_a_571_ = lean_ctor_get(v_a_567_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v_a_567_, 1);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v_a_571_);
v___x_573_ = v___x_569_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
lean_object* v_a_575_; 
lean_del_object(v___x_569_);
v_a_575_ = lean_ctor_get(v_a_567_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v_a_567_, 1);
v_a_561_ = v_a_575_;
goto v___jp_560_;
}
}
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_a_548_);
lean_dec_ref(v_d_546_);
v_a_577_ = lean_ctor_get(v___y_566_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___y_566_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___y_566_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___y_566_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___boxed(lean_object* v_upperBound_742_, lean_object* v_mvarCounterSaved_743_, lean_object* v_d_744_, lean_object* v_thm_745_, lean_object* v_a_746_, lean_object* v_b_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_upperBound_742_, v_mvarCounterSaved_743_, v_d_744_, v_thm_745_, v_a_746_, v_b_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v_thm_745_);
lean_dec(v_mvarCounterSaved_743_);
lean_dec(v_upperBound_742_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
if (lean_obj_tag(v_x_759_) == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = l_List_reverse___redArg(v_x_760_);
v___x_772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
else
{
lean_object* v_head_773_; lean_object* v_tail_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_784_; 
v_head_773_ = lean_ctor_get(v_x_759_, 0);
v_tail_774_ = lean_ctor_get(v_x_759_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_x_759_);
if (v_isSharedCheck_784_ == 0)
{
v___x_776_ = v_x_759_;
v_isShared_777_ = v_isSharedCheck_784_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_tail_774_);
lean_inc(v_head_773_);
lean_dec(v_x_759_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_784_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v_a_779_; lean_object* v___x_781_; 
v___x_778_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_head_773_, v___y_767_);
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref(v___x_778_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v_x_760_);
lean_ctor_set(v___x_776_, 0, v_a_779_);
v___x_781_ = v___x_776_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_779_);
lean_ctor_set(v_reuseFailAlloc_783_, 1, v_x_760_);
v___x_781_ = v_reuseFailAlloc_783_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
v_x_759_ = v_tail_774_;
v_x_760_ = v___x_781_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1___boxed(lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_x_785_, v_x_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object* v_thm_800_, lean_object* v_e_801_, lean_object* v_d_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; lean_object* v_mctx_814_; lean_object* v_mvarCounter_815_; lean_object* v_expr_816_; lean_object* v_pattern_817_; lean_object* v_rhs_818_; uint8_t v_perm_819_; uint8_t v___x_820_; lean_object* v___x_821_; 
v___x_813_ = lean_st_ref_get(v___y_809_);
v_mctx_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc_ref(v_mctx_814_);
lean_dec(v___x_813_);
v_mvarCounter_815_ = lean_ctor_get(v_mctx_814_, 3);
lean_inc(v_mvarCounter_815_);
lean_dec_ref(v_mctx_814_);
v_expr_816_ = lean_ctor_get(v_thm_800_, 0);
lean_inc_ref(v_expr_816_);
v_pattern_817_ = lean_ctor_get(v_thm_800_, 1);
lean_inc_ref_n(v_pattern_817_, 2);
v_rhs_818_ = lean_ctor_get(v_thm_800_, 2);
lean_inc_ref(v_rhs_818_);
v_perm_819_ = lean_ctor_get_uint8(v_thm_800_, sizeof(void*)*4);
v___x_820_ = 1;
lean_inc_ref(v_e_801_);
v___x_821_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_817_, v_e_801_, v___x_820_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_933_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_933_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_933_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_933_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
if (lean_obj_tag(v_a_822_) == 1)
{
lean_object* v_val_826_; lean_object* v_us_827_; lean_object* v_args_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_del_object(v___x_824_);
v_val_826_ = lean_ctor_get(v_a_822_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v_a_822_, 1);
v_us_827_ = lean_ctor_get(v_val_826_, 0);
lean_inc(v_us_827_);
v_args_828_ = lean_ctor_get(v_val_826_, 1);
lean_inc_ref(v_args_828_);
lean_dec(v_val_826_);
v___x_829_ = lean_array_get_size(v_args_828_);
v___x_830_ = lean_box(0);
v___x_831_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_us_827_, v___x_830_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = 0;
v___x_835_ = lean_box(0);
v___x_836_ = lean_box(v___x_834_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_args_828_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_835_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v___x_829_, v_mvarCounter_815_, v_d_802_, v_thm_800_, v___x_833_, v___x_838_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec_ref(v_thm_800_);
lean_dec(v_mvarCounter_815_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_912_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_912_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_912_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_912_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v_fst_844_; 
v_fst_844_ = lean_ctor_get(v_a_840_, 0);
if (lean_obj_tag(v_fst_844_) == 0)
{
lean_object* v_snd_845_; lean_object* v_fst_846_; lean_object* v_snd_847_; lean_object* v_levelParams_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
lean_del_object(v___x_842_);
v_snd_845_ = lean_ctor_get(v_a_840_, 1);
lean_inc(v_snd_845_);
lean_dec(v_a_840_);
v_fst_846_ = lean_ctor_get(v_snd_845_, 0);
lean_inc(v_fst_846_);
v_snd_847_ = lean_ctor_get(v_snd_845_, 1);
lean_inc(v_snd_847_);
lean_dec(v_snd_845_);
v_levelParams_848_ = lean_ctor_get(v_pattern_817_, 0);
lean_inc(v_levelParams_848_);
lean_inc(v_a_832_);
v___x_849_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(v_expr_816_, v_pattern_817_, v_a_832_, v_fst_846_);
lean_dec_ref(v_pattern_817_);
v___x_850_ = l_Lean_Expr_instantiateLevelParams(v_rhs_818_, v_levelParams_848_, v_a_832_);
lean_dec(v_a_832_);
lean_dec(v_levelParams_848_);
lean_dec_ref(v_rhs_818_);
v___x_851_ = l_Lean_Meta_Sym_shareCommonInc(v___x_850_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
v___x_853_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_a_852_, v_fst_846_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_891_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_891_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_891_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_891_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
size_t v___x_858_; size_t v___x_859_; uint8_t v___x_860_; 
v___x_858_ = lean_ptr_addr(v_e_801_);
v___x_859_ = lean_ptr_addr(v_a_854_);
v___x_860_ = lean_usize_dec_eq(v___x_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
lean_del_object(v___x_856_);
lean_inc(v_a_854_);
v___x_861_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_819_, v_e_801_, v_a_854_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_877_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_877_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_877_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_877_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
uint8_t v___x_866_; 
v___x_866_ = lean_unbox(v_a_862_);
lean_dec(v_a_862_);
if (v___x_866_ == 0)
{
uint8_t v___x_867_; lean_object* v___x_868_; lean_object* v___x_870_; 
lean_dec(v_a_854_);
lean_dec_ref(v___x_849_);
v___x_867_ = lean_unbox(v_snd_847_);
lean_dec(v_snd_847_);
v___x_868_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_867_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_868_);
v___x_870_ = v___x_864_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
else
{
lean_object* v___x_872_; uint8_t v___x_873_; lean_object* v___x_875_; 
v___x_872_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_872_, 0, v_a_854_);
lean_ctor_set(v___x_872_, 1, v___x_849_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*2, v___x_834_);
v___x_873_ = lean_unbox(v_snd_847_);
lean_dec(v_snd_847_);
lean_ctor_set_uint8(v___x_872_, sizeof(void*)*2 + 1, v___x_873_);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_872_);
v___x_875_ = v___x_864_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_872_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec(v_a_854_);
lean_dec_ref(v___x_849_);
lean_dec(v_snd_847_);
v_a_878_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_861_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_861_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
lean_dec(v_a_854_);
lean_dec_ref(v___x_849_);
lean_dec_ref(v_e_801_);
v___x_886_ = lean_unbox(v_snd_847_);
lean_dec(v_snd_847_);
v___x_887_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_886_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_887_);
v___x_889_ = v___x_856_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref(v___x_849_);
lean_dec(v_snd_847_);
lean_dec_ref(v_e_801_);
v_a_892_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_853_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_853_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec_ref(v___x_849_);
lean_dec(v_snd_847_);
lean_dec(v_fst_846_);
lean_dec_ref(v_e_801_);
v_a_900_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_851_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_851_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v_val_908_; lean_object* v___x_910_; 
lean_inc_ref(v_fst_844_);
lean_dec(v_a_840_);
lean_dec(v_a_832_);
lean_dec_ref(v_rhs_818_);
lean_dec_ref(v_pattern_817_);
lean_dec_ref(v_expr_816_);
lean_dec_ref(v_e_801_);
v_val_908_ = lean_ctor_get(v_fst_844_, 0);
lean_inc(v_val_908_);
lean_dec_ref_known(v_fst_844_, 1);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v_val_908_);
v___x_910_ = v___x_842_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_val_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec(v_a_832_);
lean_dec_ref(v_rhs_818_);
lean_dec_ref(v_pattern_817_);
lean_dec_ref(v_expr_816_);
lean_dec_ref(v_e_801_);
v_a_913_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_839_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_839_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v_args_828_);
lean_dec_ref(v_rhs_818_);
lean_dec_ref(v_pattern_817_);
lean_dec_ref(v_expr_816_);
lean_dec(v_mvarCounter_815_);
lean_dec_ref(v_d_802_);
lean_dec_ref(v_e_801_);
lean_dec_ref(v_thm_800_);
v_a_921_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_831_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_831_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v___x_929_; lean_object* v___x_931_; 
lean_dec(v_a_822_);
lean_dec_ref(v_rhs_818_);
lean_dec_ref(v_pattern_817_);
lean_dec_ref(v_expr_816_);
lean_dec(v_mvarCounter_815_);
lean_dec_ref(v_d_802_);
lean_dec_ref(v_e_801_);
lean_dec_ref(v_thm_800_);
v___x_929_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0));
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_929_);
v___x_931_ = v___x_824_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v_rhs_818_);
lean_dec_ref(v_pattern_817_);
lean_dec_ref(v_expr_816_);
lean_dec(v_mvarCounter_815_);
lean_dec_ref(v_d_802_);
lean_dec_ref(v_e_801_);
lean_dec_ref(v_thm_800_);
v_a_934_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_821_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_821_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object* v_thm_942_, lean_object* v_e_943_, lean_object* v_d_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(v_thm_942_, v_e_943_, v_d_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object* v_thm_956_, lean_object* v_e_957_, lean_object* v_d_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v___f_969_; uint8_t v___x_970_; lean_object* v___x_971_; 
v___f_969_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed), 13, 3);
lean_closure_set(v___f_969_, 0, v_thm_956_);
lean_closure_set(v___f_969_, 1, v_e_957_);
lean_closure_set(v___f_969_, 2, v_d_958_);
v___x_970_ = 0;
v___x_971_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(v___f_969_, v___x_970_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object* v_thm_972_, lean_object* v_e_973_, lean_object* v_d_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_thm_972_, v_e_973_, v_d_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(lean_object* v_mvarId_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_986_, v___y_993_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(lean_object* v_mvarId_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(v_mvarId_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec(v_mvarId_998_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(lean_object* v_mvarId_1010_, lean_object* v_val_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_1010_, v_val_1011_, v___y_1018_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(lean_object* v_mvarId_1023_, lean_object* v_val_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(v_mvarId_1023_, v_val_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(lean_object* v_upperBound_1036_, lean_object* v_mvarCounterSaved_1037_, lean_object* v_d_1038_, lean_object* v___x_1039_, lean_object* v_thm_1040_, lean_object* v_inst_1041_, lean_object* v_R_1042_, lean_object* v_a_1043_, lean_object* v_b_1044_, lean_object* v_c_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_upperBound_1036_, v_mvarCounterSaved_1037_, v_d_1038_, v_thm_1040_, v_a_1043_, v_b_1044_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_1057_ = _args[0];
lean_object* v_mvarCounterSaved_1058_ = _args[1];
lean_object* v_d_1059_ = _args[2];
lean_object* v___x_1060_ = _args[3];
lean_object* v_thm_1061_ = _args[4];
lean_object* v_inst_1062_ = _args[5];
lean_object* v_R_1063_ = _args[6];
lean_object* v_a_1064_ = _args[7];
lean_object* v_b_1065_ = _args[8];
lean_object* v_c_1066_ = _args[9];
lean_object* v___y_1067_ = _args[10];
lean_object* v___y_1068_ = _args[11];
lean_object* v___y_1069_ = _args[12];
lean_object* v___y_1070_ = _args[13];
lean_object* v___y_1071_ = _args[14];
lean_object* v___y_1072_ = _args[15];
lean_object* v___y_1073_ = _args[16];
lean_object* v___y_1074_ = _args[17];
lean_object* v___y_1075_ = _args[18];
lean_object* v___y_1076_ = _args[19];
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(v_upperBound_1057_, v_mvarCounterSaved_1058_, v_d_1059_, v___x_1060_, v_thm_1061_, v_inst_1062_, v_R_1063_, v_a_1064_, v_b_1065_, v_c_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v_thm_1061_);
lean_dec(v___x_1060_);
lean_dec(v_mvarCounterSaved_1058_);
lean_dec(v_upperBound_1057_);
return v_res_1077_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_object* v_00_u03b2_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
uint8_t v___x_1081_; 
v___x_1081_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
uint8_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(v_00_u03b2_1082_, v_x_1083_, v_x_1084_);
lean_dec(v_x_1084_);
lean_dec_ref(v_x_1083_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(lean_object* v_00_u03b2_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_x_1088_, v_x_1089_, v_x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1092_, lean_object* v_x_1093_, size_t v_x_1094_, lean_object* v_x_1095_){
_start:
{
uint8_t v___x_1096_; 
v___x_1096_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_1093_, v_x_1094_, v_x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
size_t v_x_45194__boxed_1101_; uint8_t v_res_1102_; lean_object* v_r_1103_; 
v_x_45194__boxed_1101_ = lean_unbox_usize(v_x_1099_);
lean_dec(v_x_1099_);
v_res_1102_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(v_00_u03b2_1097_, v_x_1098_, v_x_45194__boxed_1101_, v_x_1100_);
lean_dec(v_x_1100_);
lean_dec_ref(v_x_1098_);
v_r_1103_ = lean_box(v_res_1102_);
return v_r_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(lean_object* v_00_u03b2_1104_, lean_object* v_x_1105_, size_t v_x_1106_, size_t v_x_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_1105_, v_x_1106_, v_x_1107_, v_x_1108_, v_x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_){
_start:
{
size_t v_x_45205__boxed_1117_; size_t v_x_45206__boxed_1118_; lean_object* v_res_1119_; 
v_x_45205__boxed_1117_ = lean_unbox_usize(v_x_1113_);
lean_dec(v_x_1113_);
v_x_45206__boxed_1118_ = lean_unbox_usize(v_x_1114_);
lean_dec(v_x_1114_);
v_res_1119_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(v_00_u03b2_1111_, v_x_1112_, v_x_45205__boxed_1117_, v_x_45206__boxed_1118_, v_x_1115_, v_x_1116_);
return v_res_1119_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1120_, lean_object* v_keys_1121_, lean_object* v_vals_1122_, lean_object* v_heq_1123_, lean_object* v_i_1124_, lean_object* v_k_1125_){
_start:
{
uint8_t v___x_1126_; 
v___x_1126_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_keys_1121_, v_i_1124_, v_k_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1127_, lean_object* v_keys_1128_, lean_object* v_vals_1129_, lean_object* v_heq_1130_, lean_object* v_i_1131_, lean_object* v_k_1132_){
_start:
{
uint8_t v_res_1133_; lean_object* v_r_1134_; 
v_res_1133_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(v_00_u03b2_1127_, v_keys_1128_, v_vals_1129_, v_heq_1130_, v_i_1131_, v_k_1132_);
lean_dec(v_k_1132_);
lean_dec_ref(v_vals_1129_);
lean_dec_ref(v_keys_1128_);
v_r_1134_ = lean_box(v_res_1133_);
return v_r_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_1135_, lean_object* v_n_1136_, lean_object* v_k_1137_, lean_object* v_v_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11___redArg(v_n_1136_, v_k_1137_, v_v_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1140_, size_t v_depth_1141_, lean_object* v_keys_1142_, lean_object* v_vals_1143_, lean_object* v_heq_1144_, lean_object* v_i_1145_, lean_object* v_entries_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_depth_1141_, v_keys_1142_, v_vals_1143_, v_i_1145_, v_entries_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1148_, lean_object* v_depth_1149_, lean_object* v_keys_1150_, lean_object* v_vals_1151_, lean_object* v_heq_1152_, lean_object* v_i_1153_, lean_object* v_entries_1154_){
_start:
{
size_t v_depth_boxed_1155_; lean_object* v_res_1156_; 
v_depth_boxed_1155_ = lean_unbox_usize(v_depth_1149_);
lean_dec(v_depth_1149_);
v_res_1156_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(v_00_u03b2_1148_, v_depth_boxed_1155_, v_keys_1150_, v_vals_1151_, v_heq_1152_, v_i_1153_, v_entries_1154_);
lean_dec_ref(v_vals_1151_);
lean_dec_ref(v_keys_1150_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1157_, lean_object* v_x_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12___redArg(v_x_1158_, v_x_1159_, v_x_1160_, v_x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0(lean_object* v_fst_1163_, lean_object* v_d_1164_, lean_object* v_x_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1163_, v_x_1165_, v_d_1164_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0___boxed(lean_object* v_fst_1177_, lean_object* v_d_1178_, lean_object* v_x_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0(v_fst_1177_, v_d_1178_, v_x_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0(lean_object* v_d_1191_, lean_object* v_e_1192_, lean_object* v_as_1193_, size_t v_sz_1194_, size_t v_i_1195_, lean_object* v_b_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
uint8_t v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1217_; uint8_t v___y_1218_; lean_object* v___y_1221_; uint8_t v___y_1222_; uint8_t v___y_1223_; uint8_t v___y_1224_; lean_object* v___y_1226_; uint8_t v___y_1227_; uint8_t v___y_1228_; lean_object* v___y_1232_; uint8_t v___y_1233_; uint8_t v___x_1235_; 
v___x_1235_ = lean_usize_dec_lt(v_i_1195_, v_sz_1194_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_dec_ref(v_e_1192_);
lean_dec_ref(v_d_1191_);
v___x_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_b_1196_);
return v___x_1236_;
}
else
{
lean_object* v_a_1237_; lean_object* v_fst_1238_; lean_object* v_snd_1239_; lean_object* v_snd_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1289_; 
v_a_1237_ = lean_array_uget_borrowed(v_as_1193_, v_i_1195_);
v_fst_1238_ = lean_ctor_get(v_a_1237_, 0);
v_snd_1239_ = lean_ctor_get(v_a_1237_, 1);
v_snd_1240_ = lean_ctor_get(v_b_1196_, 1);
v_isSharedCheck_1289_ = !lean_is_exclusive(v_b_1196_);
if (v_isSharedCheck_1289_ == 0)
{
lean_object* v_unused_1290_; 
v_unused_1290_ = lean_ctor_get(v_b_1196_, 0);
lean_dec(v_unused_1290_);
v___x_1242_ = v_b_1196_;
v_isShared_1243_ = v_isSharedCheck_1289_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_snd_1240_);
lean_dec(v_b_1196_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1289_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v___y_1246_; uint8_t v_done_1247_; uint8_t v___y_1248_; lean_object* v_result_1258_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v___x_1244_ = lean_box(0);
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = lean_nat_dec_eq(v_snd_1239_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___f_1268_; lean_object* v___x_1269_; 
lean_inc_ref(v_d_1191_);
lean_inc(v_fst_1238_);
v___f_1268_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1268_, 0, v_fst_1238_);
lean_closure_set(v___f_1268_, 1, v_d_1191_);
lean_inc_ref(v_e_1192_);
v___x_1269_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_1192_, v_snd_1239_, v___f_1268_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_a_1270_);
lean_dec_ref_known(v___x_1269_, 1);
v_result_1258_ = v_a_1270_;
goto v___jp_1257_;
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
lean_dec_ref(v_e_1192_);
lean_dec_ref(v_d_1191_);
v_a_1271_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1269_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1269_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v___x_1279_; 
lean_inc_ref(v_d_1191_);
lean_inc_ref(v_e_1192_);
lean_inc(v_fst_1238_);
v___x_1279_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1238_, v_e_1192_, v_d_1191_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v_result_1258_ = v_a_1280_;
goto v___jp_1257_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
lean_dec_ref(v_e_1192_);
lean_dec_ref(v_d_1191_);
v_a_1281_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1279_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1279_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
v___jp_1245_:
{
if (v_done_1247_ == 0)
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
lean_dec_ref(v___y_1246_);
v___x_1249_ = lean_box(v___y_1248_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1249_);
lean_ctor_set(v___x_1242_, 0, v___x_1244_);
v___x_1251_ = v___x_1242_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1255_, 1, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
size_t v___x_1252_; size_t v___x_1253_; 
v___x_1252_ = ((size_t)1ULL);
v___x_1253_ = lean_usize_add(v_i_1195_, v___x_1252_);
v_i_1195_ = v___x_1253_;
v_b_1196_ = v___x_1251_;
goto _start;
}
}
else
{
uint8_t v___x_1256_; 
lean_del_object(v___x_1242_);
lean_dec_ref(v_e_1192_);
lean_dec_ref(v_d_1191_);
v___x_1256_ = 0;
v___y_1226_ = v___y_1246_;
v___y_1227_ = v___y_1248_;
v___y_1228_ = v___x_1256_;
goto v___jp_1225_;
}
}
v___jp_1257_:
{
uint8_t v___x_1259_; 
v___x_1259_ = lean_unbox(v_snd_1240_);
if (v___x_1259_ == 0)
{
lean_dec(v_snd_1240_);
if (lean_obj_tag(v_result_1258_) == 0)
{
uint8_t v_done_1260_; uint8_t v_contextDependent_1261_; 
v_done_1260_ = lean_ctor_get_uint8(v_result_1258_, 0);
v_contextDependent_1261_ = lean_ctor_get_uint8(v_result_1258_, 1);
v___y_1246_ = v_result_1258_;
v_done_1247_ = v_done_1260_;
v___y_1248_ = v_contextDependent_1261_;
goto v___jp_1245_;
}
else
{
uint8_t v_contextDependent_1262_; 
lean_del_object(v___x_1242_);
lean_dec_ref(v_e_1192_);
lean_dec_ref(v_d_1191_);
v_contextDependent_1262_ = lean_ctor_get_uint8(v_result_1258_, sizeof(void*)*2 + 1);
v___y_1232_ = v_result_1258_;
v___y_1233_ = v_contextDependent_1262_;
goto v___jp_1231_;
}
}
else
{
if (lean_obj_tag(v_result_1258_) == 0)
{
uint8_t v_done_1263_; uint8_t v___x_1264_; 
v_done_1263_ = lean_ctor_get_uint8(v_result_1258_, 0);
v___x_1264_ = lean_unbox(v_snd_1240_);
lean_dec(v_snd_1240_);
v___y_1246_ = v_result_1258_;
v_done_1247_ = v_done_1263_;
v___y_1248_ = v___x_1264_;
goto v___jp_1245_;
}
else
{
uint8_t v___x_1265_; 
lean_del_object(v___x_1242_);
lean_dec_ref(v_e_1192_);
lean_dec_ref(v_d_1191_);
v___x_1265_ = lean_unbox(v_snd_1240_);
lean_dec(v_snd_1240_);
v___y_1232_ = v_result_1258_;
v___y_1233_ = v___x_1265_;
goto v___jp_1231_;
}
}
}
}
}
v___jp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1210_ = lean_box(v___y_1208_);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___y_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
v___x_1213_ = lean_box(v___y_1208_);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
return v___x_1215_;
}
v___jp_1216_:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1217_);
v___y_1208_ = v___y_1218_;
v___y_1209_ = v___x_1219_;
goto v___jp_1207_;
}
v___jp_1220_:
{
if (v___y_1224_ == 0)
{
v___y_1217_ = v___y_1221_;
v___y_1218_ = v___y_1223_;
goto v___jp_1216_;
}
else
{
if (v___y_1222_ == 0)
{
v___y_1208_ = v___y_1223_;
v___y_1209_ = v___y_1221_;
goto v___jp_1207_;
}
else
{
v___y_1217_ = v___y_1221_;
v___y_1218_ = v___y_1223_;
goto v___jp_1216_;
}
}
}
v___jp_1225_:
{
if (v___y_1227_ == 0)
{
v___y_1208_ = v___y_1227_;
v___y_1209_ = v___y_1226_;
goto v___jp_1207_;
}
else
{
if (lean_obj_tag(v___y_1226_) == 0)
{
uint8_t v_contextDependent_1229_; 
v_contextDependent_1229_ = lean_ctor_get_uint8(v___y_1226_, 1);
v___y_1221_ = v___y_1226_;
v___y_1222_ = v___y_1228_;
v___y_1223_ = v___y_1227_;
v___y_1224_ = v_contextDependent_1229_;
goto v___jp_1220_;
}
else
{
uint8_t v_contextDependent_1230_; 
v_contextDependent_1230_ = lean_ctor_get_uint8(v___y_1226_, sizeof(void*)*2 + 1);
v___y_1221_ = v___y_1226_;
v___y_1222_ = v___y_1228_;
v___y_1223_ = v___y_1227_;
v___y_1224_ = v_contextDependent_1230_;
goto v___jp_1220_;
}
}
}
v___jp_1231_:
{
uint8_t v___x_1234_; 
v___x_1234_ = 0;
v___y_1226_ = v___y_1232_;
v___y_1227_ = v___y_1233_;
v___y_1228_ = v___x_1234_;
goto v___jp_1225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0___boxed(lean_object* v_d_1291_, lean_object* v_e_1292_, lean_object* v_as_1293_, lean_object* v_sz_1294_, lean_object* v_i_1295_, lean_object* v_b_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1294_);
lean_dec(v_sz_1294_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1295_);
lean_dec(v_i_1295_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0(v_d_1291_, v_e_1292_, v_as_1293_, v_sz_boxed_1307_, v_i_boxed_1308_, v_b_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v_as_1293_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing(lean_object* v_candidates_1310_, lean_object* v_e_1311_, lean_object* v_d_1312_, uint8_t v_anyCD_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; size_t v_sz_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
v___x_1324_ = lean_box(0);
v___x_1325_ = lean_box(v_anyCD_1313_);
v___x_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v_sz_1327_ = lean_array_size(v_candidates_1310_);
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing_spec__0(v_d_1312_, v_e_1311_, v_candidates_1310_, v_sz_1327_, v___x_1328_, v___x_1326_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1353_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1353_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1353_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v_fst_1334_; 
v_fst_1334_ = lean_ctor_get(v_a_1330_, 0);
if (lean_obj_tag(v_fst_1334_) == 0)
{
lean_object* v_snd_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1347_; 
v_snd_1335_ = lean_ctor_get(v_a_1330_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_a_1330_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v_a_1330_, 0);
lean_dec(v_unused_1348_);
v___x_1337_ = v_a_1330_;
v_isShared_1338_ = v_isSharedCheck_1347_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_snd_1335_);
lean_dec(v_a_1330_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1347_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1339_ = lean_unbox(v_snd_1335_);
v___x_1340_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1339_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 0, v___x_1340_);
v___x_1342_ = v___x_1337_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_snd_1335_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v___x_1342_);
v___x_1344_ = v___x_1332_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
else
{
lean_object* v_val_1349_; lean_object* v___x_1351_; 
lean_inc_ref(v_fst_1334_);
lean_dec(v_a_1330_);
v_val_1349_ = lean_ctor_get(v_fst_1334_, 0);
lean_inc(v_val_1349_);
lean_dec_ref_known(v_fst_1334_, 1);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v_val_1349_);
v___x_1351_ = v___x_1332_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_val_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_a_1354_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1329_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1329_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing___boxed(lean_object* v_candidates_1362_, lean_object* v_e_1363_, lean_object* v_d_1364_, lean_object* v_anyCD_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_){
_start:
{
uint8_t v_anyCD_boxed_1376_; lean_object* v_res_1377_; 
v_anyCD_boxed_1376_ = lean_unbox(v_anyCD_1365_);
v_res_1377_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing(v_candidates_1362_, v_e_1363_, v_d_1364_, v_anyCD_boxed_1376_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_candidates_1362_);
return v_res_1377_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___redArg(lean_object* v_x_1378_){
_start:
{
uint8_t v___x_1379_; 
v___x_1379_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___redArg___boxed(lean_object* v_x_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___redArg(v_x_1380_);
lean_dec_ref(v_x_1380_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object* v_00_u03b2_1383_, lean_object* v_x_1384_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object* v_00_u03b2_1386_, lean_object* v_x_1387_){
_start:
{
uint8_t v_res_1388_; lean_object* v_r_1389_; 
v_res_1388_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_00_u03b2_1386_, v_x_1387_);
lean_dec_ref(v_x_1387_);
v_r_1389_ = lean_box(v_res_1388_);
return v_r_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object* v_thms_1390_, lean_object* v_d_1391_, lean_object* v_e_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1403_; lean_object* v_mctx_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; lean_object* v___x_1407_; 
v___x_1403_ = lean_st_ref_get(v_a_1399_);
v_mctx_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc_ref(v_mctx_1404_);
lean_dec(v___x_1403_);
v___x_1405_ = l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(v_thms_1390_, v_mctx_1404_, v_e_1392_);
v___x_1406_ = 0;
lean_inc_ref(v_d_1391_);
lean_inc_ref(v_e_1392_);
v___x_1407_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing(v___x_1405_, v_e_1392_, v_d_1391_, v___x_1406_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
lean_dec_ref(v___x_1405_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1446_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1446_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1446_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_fst_1412_; 
v_fst_1412_ = lean_ctor_get(v_a_1408_, 0);
lean_inc(v_fst_1412_);
if (lean_obj_tag(v_fst_1412_) == 0)
{
uint8_t v_done_1413_; 
v_done_1413_ = lean_ctor_get_uint8(v_fst_1412_, 0);
if (v_done_1413_ == 0)
{
lean_object* v_snd_1414_; lean_object* v_fallback_1415_; uint8_t v___x_1416_; 
v_snd_1414_ = lean_ctor_get(v_a_1408_, 1);
lean_inc(v_snd_1414_);
lean_dec(v_a_1408_);
v_fallback_1415_ = lean_ctor_get(v_thms_1390_, 1);
v___x_1416_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_fallback_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; uint8_t v___x_1418_; lean_object* v___x_1419_; 
lean_dec_ref_known(v_fst_1412_, 0);
lean_del_object(v___x_1410_);
v___x_1417_ = l_Lean_Meta_Sym_Simp_Theorems_getFallbackMatchWithExtra(v_thms_1390_, v_mctx_1404_, v_e_1392_);
lean_dec_ref(v_mctx_1404_);
v___x_1418_ = lean_unbox(v_snd_1414_);
lean_dec(v_snd_1414_);
v___x_1419_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_rewriteUsing(v___x_1417_, v_e_1392_, v_d_1391_, v___x_1418_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
lean_dec_ref(v___x_1417_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1428_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1428_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1428_ == 0)
{
v___x_1422_ = v___x_1419_;
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_a_1420_);
lean_dec(v___x_1419_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1428_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_fst_1424_; lean_object* v___x_1426_; 
v_fst_1424_ = lean_ctor_get(v_a_1420_, 0);
lean_inc(v_fst_1424_);
lean_dec(v_a_1420_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 0, v_fst_1424_);
v___x_1426_ = v___x_1422_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_fst_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
v_a_1429_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1419_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1419_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
else
{
lean_object* v___x_1438_; 
lean_dec(v_snd_1414_);
lean_dec_ref(v_mctx_1404_);
lean_dec_ref(v_e_1392_);
lean_dec_ref(v_d_1391_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v_fst_1412_);
v___x_1438_ = v___x_1410_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_fst_1412_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
else
{
lean_object* v___x_1441_; 
lean_dec(v_a_1408_);
lean_dec_ref(v_mctx_1404_);
lean_dec_ref(v_e_1392_);
lean_dec_ref(v_d_1391_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v_fst_1412_);
v___x_1441_ = v___x_1410_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_fst_1412_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
else
{
lean_object* v___x_1444_; 
lean_dec(v_a_1408_);
lean_dec_ref(v_mctx_1404_);
lean_dec_ref(v_e_1392_);
lean_dec_ref(v_d_1391_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v_fst_1412_);
v___x_1444_ = v___x_1410_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_fst_1412_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref(v_mctx_1404_);
lean_dec_ref(v_e_1392_);
lean_dec_ref(v_d_1391_);
v_a_1447_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1407_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1407_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object* v_thms_1455_, lean_object* v_d_1456_, lean_object* v_e_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_thms_1455_, v_d_1456_, v_e_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec_ref(v_thms_1455_);
return v_res_1468_;
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
