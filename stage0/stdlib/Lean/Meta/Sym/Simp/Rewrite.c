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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(lean_object*, lean_object*, lean_object*);
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
return v___x_240_;
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
size_t v_x_48014__boxed_271_; uint8_t v_res_272_; lean_object* v_r_273_; 
v_x_48014__boxed_271_ = lean_unbox_usize(v_x_269_);
lean_dec(v_x_269_);
v_res_272_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_268_, v_x_48014__boxed_271_, v_x_270_);
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
v___x_331_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
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
lean_object* v_ks_383_; lean_object* v_vs_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_404_; 
v_ks_383_ = lean_ctor_get(v_x_332_, 0);
v_vs_384_ = lean_ctor_get(v_x_332_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_x_332_);
if (v_isSharedCheck_404_ == 0)
{
v___x_386_ = v_x_332_;
v_isShared_387_ = v_isSharedCheck_404_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_vs_384_);
lean_inc(v_ks_383_);
lean_dec(v_x_332_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_404_;
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
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_ks_383_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_vs_384_);
v___x_389_ = v_reuseFailAlloc_403_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v_newNode_390_; uint8_t v___y_392_; size_t v___x_398_; uint8_t v___x_399_; 
v_newNode_390_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11___redArg(v___x_389_, v_x_335_, v_x_336_);
v___x_398_ = ((size_t)7ULL);
v___x_399_ = lean_usize_dec_le(v___x_398_, v_x_334_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_400_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_390_);
v___x_401_ = lean_unsigned_to_nat(4u);
v___x_402_ = lean_nat_dec_lt(v___x_400_, v___x_401_);
lean_dec(v___x_400_);
v___y_392_ = v___x_402_;
goto v___jp_391_;
}
else
{
v___y_392_ = v___x_399_;
goto v___jp_391_;
}
v___jp_391_:
{
if (v___y_392_ == 0)
{
lean_object* v_ks_393_; lean_object* v_vs_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_ks_393_ = lean_ctor_get(v_newNode_390_, 0);
lean_inc_ref(v_ks_393_);
v_vs_394_ = lean_ctor_get(v_newNode_390_, 1);
lean_inc_ref(v_vs_394_);
lean_dec_ref(v_newNode_390_);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___closed__0);
v___x_397_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_x_334_, v_ks_393_, v_vs_394_, v___x_395_, v___x_396_);
lean_dec_ref(v_vs_394_);
lean_dec_ref(v_ks_393_);
return v___x_397_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(size_t v_depth_405_, lean_object* v_keys_406_, lean_object* v_vals_407_, lean_object* v_i_408_, lean_object* v_entries_409_){
_start:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_array_get_size(v_keys_406_);
v___x_411_ = lean_nat_dec_lt(v_i_408_, v___x_410_);
if (v___x_411_ == 0)
{
lean_dec(v_i_408_);
return v_entries_409_;
}
else
{
lean_object* v_k_412_; lean_object* v_v_413_; uint64_t v___x_414_; size_t v_h_415_; size_t v___x_416_; lean_object* v___x_417_; size_t v___x_418_; size_t v___x_419_; size_t v___x_420_; size_t v_h_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_k_412_ = lean_array_fget_borrowed(v_keys_406_, v_i_408_);
v_v_413_ = lean_array_fget_borrowed(v_vals_407_, v_i_408_);
v___x_414_ = l_Lean_instHashableMVarId_hash(v_k_412_);
v_h_415_ = lean_uint64_to_usize(v___x_414_);
v___x_416_ = ((size_t)5ULL);
v___x_417_ = lean_unsigned_to_nat(1u);
v___x_418_ = ((size_t)1ULL);
v___x_419_ = lean_usize_sub(v_depth_405_, v___x_418_);
v___x_420_ = lean_usize_mul(v___x_416_, v___x_419_);
v_h_421_ = lean_usize_shift_right(v_h_415_, v___x_420_);
v___x_422_ = lean_nat_add(v_i_408_, v___x_417_);
lean_dec(v_i_408_);
lean_inc(v_v_413_);
lean_inc(v_k_412_);
v___x_423_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_entries_409_, v_h_421_, v_depth_405_, v_k_412_, v_v_413_);
v_i_408_ = v___x_422_;
v_entries_409_ = v___x_423_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_depth_425_, lean_object* v_keys_426_, lean_object* v_vals_427_, lean_object* v_i_428_, lean_object* v_entries_429_){
_start:
{
size_t v_depth_boxed_430_; lean_object* v_res_431_; 
v_depth_boxed_430_ = lean_unbox_usize(v_depth_425_);
lean_dec(v_depth_425_);
v_res_431_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_depth_boxed_430_, v_keys_426_, v_vals_427_, v_i_428_, v_entries_429_);
lean_dec_ref(v_vals_427_);
lean_dec_ref(v_keys_426_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg___boxed(lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_x_436_){
_start:
{
size_t v_x_48157__boxed_437_; size_t v_x_48158__boxed_438_; lean_object* v_res_439_; 
v_x_48157__boxed_437_ = lean_unbox_usize(v_x_433_);
lean_dec(v_x_433_);
v_x_48158__boxed_438_ = lean_unbox_usize(v_x_434_);
lean_dec(v_x_434_);
v_res_439_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_432_, v_x_48157__boxed_437_, v_x_48158__boxed_438_, v_x_435_, v_x_436_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_){
_start:
{
uint64_t v___x_443_; size_t v___x_444_; size_t v___x_445_; lean_object* v___x_446_; 
v___x_443_ = l_Lean_instHashableMVarId_hash(v_x_441_);
v___x_444_ = lean_uint64_to_usize(v___x_443_);
v___x_445_ = ((size_t)1ULL);
v___x_446_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_440_, v___x_444_, v___x_445_, v_x_441_, v_x_442_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(lean_object* v_mvarId_447_, lean_object* v_val_448_, lean_object* v___y_449_){
_start:
{
lean_object* v___x_451_; lean_object* v_mctx_452_; lean_object* v_cache_453_; lean_object* v_zetaDeltaFVarIds_454_; lean_object* v_postponed_455_; lean_object* v_diag_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_485_; 
v___x_451_ = lean_st_ref_take(v___y_449_);
v_mctx_452_ = lean_ctor_get(v___x_451_, 0);
v_cache_453_ = lean_ctor_get(v___x_451_, 1);
v_zetaDeltaFVarIds_454_ = lean_ctor_get(v___x_451_, 2);
v_postponed_455_ = lean_ctor_get(v___x_451_, 3);
v_diag_456_ = lean_ctor_get(v___x_451_, 4);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_485_ == 0)
{
v___x_458_ = v___x_451_;
v_isShared_459_ = v_isSharedCheck_485_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_diag_456_);
lean_inc(v_postponed_455_);
lean_inc(v_zetaDeltaFVarIds_454_);
lean_inc(v_cache_453_);
lean_inc(v_mctx_452_);
lean_dec(v___x_451_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_485_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_depth_460_; lean_object* v_levelAssignDepth_461_; lean_object* v_lmvarCounter_462_; lean_object* v_mvarCounter_463_; lean_object* v_lDecls_464_; lean_object* v_decls_465_; lean_object* v_userNames_466_; lean_object* v_lAssignment_467_; lean_object* v_eAssignment_468_; lean_object* v_dAssignment_469_; lean_object* v_instanceTypedMVars_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_484_; 
v_depth_460_ = lean_ctor_get(v_mctx_452_, 0);
v_levelAssignDepth_461_ = lean_ctor_get(v_mctx_452_, 1);
v_lmvarCounter_462_ = lean_ctor_get(v_mctx_452_, 2);
v_mvarCounter_463_ = lean_ctor_get(v_mctx_452_, 3);
v_lDecls_464_ = lean_ctor_get(v_mctx_452_, 4);
v_decls_465_ = lean_ctor_get(v_mctx_452_, 5);
v_userNames_466_ = lean_ctor_get(v_mctx_452_, 6);
v_lAssignment_467_ = lean_ctor_get(v_mctx_452_, 7);
v_eAssignment_468_ = lean_ctor_get(v_mctx_452_, 8);
v_dAssignment_469_ = lean_ctor_get(v_mctx_452_, 9);
v_instanceTypedMVars_470_ = lean_ctor_get(v_mctx_452_, 10);
v_isSharedCheck_484_ = !lean_is_exclusive(v_mctx_452_);
if (v_isSharedCheck_484_ == 0)
{
v___x_472_ = v_mctx_452_;
v_isShared_473_ = v_isSharedCheck_484_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_instanceTypedMVars_470_);
lean_inc(v_dAssignment_469_);
lean_inc(v_eAssignment_468_);
lean_inc(v_lAssignment_467_);
lean_inc(v_userNames_466_);
lean_inc(v_decls_465_);
lean_inc(v_lDecls_464_);
lean_inc(v_mvarCounter_463_);
lean_inc(v_lmvarCounter_462_);
lean_inc(v_levelAssignDepth_461_);
lean_inc(v_depth_460_);
lean_dec(v_mctx_452_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_484_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_eAssignment_468_, v_mvarId_447_, v_val_448_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 8, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_depth_460_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_levelAssignDepth_461_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v_lmvarCounter_462_);
lean_ctor_set(v_reuseFailAlloc_483_, 3, v_mvarCounter_463_);
lean_ctor_set(v_reuseFailAlloc_483_, 4, v_lDecls_464_);
lean_ctor_set(v_reuseFailAlloc_483_, 5, v_decls_465_);
lean_ctor_set(v_reuseFailAlloc_483_, 6, v_userNames_466_);
lean_ctor_set(v_reuseFailAlloc_483_, 7, v_lAssignment_467_);
lean_ctor_set(v_reuseFailAlloc_483_, 8, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_483_, 9, v_dAssignment_469_);
lean_ctor_set(v_reuseFailAlloc_483_, 10, v_instanceTypedMVars_470_);
v___x_476_ = v_reuseFailAlloc_483_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_478_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_476_);
v___x_478_ = v___x_458_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_cache_453_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_zetaDeltaFVarIds_454_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_postponed_455_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_diag_456_);
v___x_478_ = v_reuseFailAlloc_482_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_st_ref_put(v___y_449_, v___x_478_);
v___x_480_ = lean_box(0);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
return v___x_481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(lean_object* v_mvarId_486_, lean_object* v_val_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_486_, v_val_487_, v___y_488_);
lean_dec(v___y_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(lean_object* v_mvarId_491_, lean_object* v_fst_492_, lean_object* v_a_493_, uint8_t v___y_494_, lean_object* v___x_495_, lean_object* v_val_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; 
lean_inc_ref(v_val_496_);
v___x_507_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_491_, v_val_496_, v___y_503_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_519_; 
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v___x_507_, 0);
lean_dec(v_unused_520_);
v___x_509_ = v___x_507_;
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
else
{
lean_dec(v___x_507_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_519_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_511_ = lean_array_fset(v_fst_492_, v_a_493_, v_val_496_);
v___x_512_ = lean_box(v___y_494_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_495_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_515_);
v___x_517_ = v___x_509_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref(v_val_496_);
lean_dec(v___x_495_);
lean_dec(v_fst_492_);
v_a_521_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_507_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_507_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed(lean_object* v_mvarId_529_, lean_object* v_fst_530_, lean_object* v_a_531_, lean_object* v___y_532_, lean_object* v___x_533_, lean_object* v_val_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
uint8_t v___y_48371__boxed_545_; lean_object* v_res_546_; 
v___y_48371__boxed_545_ = lean_unbox(v___y_532_);
v_res_546_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_529_, v_fst_530_, v_a_531_, v___y_48371__boxed_545_, v___x_533_, v_val_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec(v_a_531_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(lean_object* v_upperBound_547_, lean_object* v_mvarCounterSaved_548_, lean_object* v_d_549_, lean_object* v_thm_550_, lean_object* v_a_551_, lean_object* v_b_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_a_564_; lean_object* v___y_569_; uint8_t v___x_588_; 
v___x_588_ = lean_nat_dec_lt(v_a_551_, v_upperBound_547_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v___x_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_589_, 0, v_b_552_);
return v___x_589_;
}
else
{
lean_object* v_snd_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_743_; 
v_snd_590_ = lean_ctor_get(v_b_552_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_b_552_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v_b_552_, 0);
lean_dec(v_unused_744_);
v___x_592_ = v_b_552_;
v_isShared_593_ = v_isSharedCheck_743_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_snd_590_);
lean_dec(v_b_552_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_743_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_742_; 
v_fst_594_ = lean_ctor_get(v_snd_590_, 0);
v_snd_595_ = lean_ctor_get(v_snd_590_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_snd_590_);
if (v_isSharedCheck_742_ == 0)
{
v___x_597_ = v_snd_590_;
v_isShared_598_ = v_isSharedCheck_742_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_snd_595_);
lean_inc(v_fst_594_);
lean_dec(v_snd_590_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_742_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = lean_box(0);
v___x_600_ = lean_array_fget_borrowed(v_fst_594_, v_a_551_);
if (lean_obj_tag(v___x_600_) == 2)
{
lean_object* v_mvarId_601_; lean_object* v___x_602_; 
v_mvarId_601_ = lean_ctor_get(v___x_600_, 0);
v___x_602_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_601_, v___y_559_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; uint8_t v___x_604_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_a_603_);
lean_dec_ref_known(v___x_602_, 1);
v___x_604_ = lean_unbox(v_a_603_);
lean_dec(v_a_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_inc(v_mvarId_601_);
v___x_605_ = l_Lean_MVarId_getDecl(v_mvarId_601_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v_type_607_; lean_object* v_index_608_; uint8_t v___x_609_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_a_606_);
lean_dec_ref_known(v___x_605_, 1);
v_type_607_ = lean_ctor_get(v_a_606_, 2);
lean_inc_ref(v_type_607_);
v_index_608_ = lean_ctor_get(v_a_606_, 6);
lean_inc(v_index_608_);
lean_dec(v_a_606_);
v___x_609_ = lean_nat_dec_le(v_mvarCounterSaved_548_, v_index_608_);
lean_dec(v_index_608_);
if (v___x_609_ == 0)
{
lean_object* v___x_611_; 
lean_dec_ref(v_type_607_);
if (v_isShared_598_ == 0)
{
v___x_611_ = v___x_597_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_fst_594_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_snd_595_);
v___x_611_ = v_reuseFailAlloc_615_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_611_);
lean_ctor_set(v___x_592_, 0, v___x_599_);
v___x_613_ = v___x_592_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
v_a_564_ = v___x_613_;
goto v___jp_563_;
}
}
}
else
{
lean_object* v___x_616_; 
lean_inc_ref(v_d_549_);
lean_inc(v___y_561_);
lean_inc_ref(v___y_560_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___y_557_);
lean_inc_ref(v___y_556_);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
v___x_616_ = lean_apply_11(v_d_549_, v_type_607_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, lean_box(0));
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_676_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_676_ == 0)
{
v___x_619_ = v___x_616_;
v_isShared_620_ = v_isSharedCheck_676_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_676_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
uint8_t v___y_622_; 
if (lean_obj_tag(v_a_617_) == 0)
{
uint8_t v___x_635_; 
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v___x_635_ = lean_unbox(v_snd_595_);
lean_dec(v_snd_595_);
if (v___x_635_ == 0)
{
uint8_t v_contextDependent_636_; 
v_contextDependent_636_ = lean_ctor_get_uint8(v_a_617_, 0);
lean_dec_ref_known(v_a_617_, 0);
v___y_622_ = v_contextDependent_636_;
goto v___jp_621_;
}
else
{
lean_dec_ref_known(v_a_617_, 0);
v___y_622_ = v___x_609_;
goto v___jp_621_;
}
}
else
{
lean_object* v_proof_637_; uint8_t v_contextDependent_638_; uint8_t v___y_640_; uint8_t v___x_675_; 
lean_inc(v_mvarId_601_);
lean_del_object(v___x_619_);
lean_del_object(v___x_597_);
lean_del_object(v___x_592_);
v_proof_637_ = lean_ctor_get(v_a_617_, 0);
lean_inc_ref(v_proof_637_);
v_contextDependent_638_ = lean_ctor_get_uint8(v_a_617_, sizeof(void*)*1);
lean_dec_ref_known(v_a_617_, 1);
v___x_675_ = lean_unbox(v_snd_595_);
lean_dec(v_snd_595_);
if (v___x_675_ == 0)
{
v___y_640_ = v_contextDependent_638_;
goto v___jp_639_;
}
else
{
v___y_640_ = v___x_609_;
goto v___jp_639_;
}
v___jp_639_:
{
lean_object* v_rhsVarMask_641_; uint8_t v___x_642_; 
v_rhsVarMask_641_ = lean_ctor_get(v_thm_550_, 3);
v___x_642_ = l_Nat_testBit(v_rhsVarMask_641_, v_a_551_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_proof_637_, v___y_559_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_601_, v_fst_594_, v_a_551_, v___y_640_, v___x_599_, v_a_644_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
v___y_569_ = v___x_645_;
goto v___jp_568_;
}
else
{
lean_object* v_a_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_mvarId_601_);
lean_dec(v_fst_594_);
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v_a_646_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_653_ == 0)
{
v___x_648_ = v___x_643_;
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_a_646_);
lean_dec(v___x_643_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_653_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_651_; 
if (v_isShared_649_ == 0)
{
v___x_651_ = v___x_648_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_a_646_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
else
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_proof_637_, v___y_559_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = l_Lean_Meta_Sym_shareCommon(v_a_655_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_658_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v___x_658_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_601_, v_fst_594_, v_a_551_, v___y_640_, v___x_599_, v_a_657_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
v___y_569_ = v___x_658_;
goto v___jp_568_;
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec(v_mvarId_601_);
lean_dec(v_fst_594_);
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v_a_659_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_656_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_656_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec(v_mvarId_601_);
lean_dec(v_fst_594_);
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v_a_667_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_654_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_654_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
}
}
v___jp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_623_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_622_);
v___x_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
v___x_625_ = lean_box(v___y_622_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 1, v___x_625_);
v___x_627_ = v___x_597_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_fst_594_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_625_);
v___x_627_ = v_reuseFailAlloc_634_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_627_);
lean_ctor_set(v___x_592_, 0, v___x_624_);
v___x_629_ = v___x_592_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_624_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_627_);
v___x_629_ = v_reuseFailAlloc_633_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_629_);
v___x_631_ = v___x_619_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
else
{
lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_del_object(v___x_597_);
lean_dec(v_snd_595_);
lean_dec(v_fst_594_);
lean_del_object(v___x_592_);
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v_a_677_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_616_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_616_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
else
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
lean_del_object(v___x_597_);
lean_dec(v_snd_595_);
lean_dec(v_fst_594_);
lean_del_object(v___x_592_);
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v_a_685_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_605_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_605_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v___x_693_; 
lean_inc_ref(v___x_600_);
v___x_693_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_600_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = lean_array_fset(v_fst_594_, v_a_551_, v_a_694_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_695_);
v___x_697_ = v___x_597_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_snd_595_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_697_);
lean_ctor_set(v___x_592_, 0, v___x_599_);
v___x_699_ = v___x_592_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
v_a_564_ = v___x_699_;
goto v___jp_563_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_del_object(v___x_597_);
lean_dec(v_snd_595_);
lean_dec(v_fst_594_);
lean_del_object(v___x_592_);
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v_a_702_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_693_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_693_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_del_object(v___x_597_);
lean_dec(v_snd_595_);
lean_dec(v_fst_594_);
lean_del_object(v___x_592_);
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v_a_710_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_602_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_602_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
uint8_t v___x_718_; 
v___x_718_ = l_Lean_Expr_hasMVar(v___x_600_);
if (v___x_718_ == 0)
{
lean_object* v___x_720_; 
if (v_isShared_598_ == 0)
{
v___x_720_ = v___x_597_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_fst_594_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_snd_595_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_720_);
lean_ctor_set(v___x_592_, 0, v___x_599_);
v___x_722_ = v___x_592_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
v_a_564_ = v___x_722_;
goto v___jp_563_;
}
}
}
else
{
lean_object* v___x_725_; 
lean_inc(v___x_600_);
v___x_725_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_600_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
v___x_727_ = lean_array_fset(v_fst_594_, v_a_551_, v_a_726_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_727_);
v___x_729_ = v___x_597_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_snd_595_);
v___x_729_ = v_reuseFailAlloc_733_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_731_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 1, v___x_729_);
lean_ctor_set(v___x_592_, 0, v___x_599_);
v___x_731_ = v___x_592_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_599_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
v_a_564_ = v___x_731_;
goto v___jp_563_;
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_del_object(v___x_597_);
lean_dec(v_snd_595_);
lean_dec(v_fst_594_);
lean_del_object(v___x_592_);
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v_a_734_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_725_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_725_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
}
}
v___jp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(1u);
v___x_566_ = lean_nat_add(v_a_551_, v___x_565_);
lean_dec(v_a_551_);
v_a_551_ = v___x_566_;
v_b_552_ = v_a_564_;
goto _start;
}
v___jp_568_:
{
if (lean_obj_tag(v___y_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_579_; 
v_a_570_ = lean_ctor_get(v___y_569_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___y_569_);
if (v_isSharedCheck_579_ == 0)
{
v___x_572_ = v___y_569_;
v_isShared_573_ = v_isSharedCheck_579_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___y_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_579_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
if (lean_obj_tag(v_a_570_) == 0)
{
lean_object* v_a_574_; lean_object* v___x_576_; 
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v_a_574_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_a_574_);
lean_dec_ref_known(v_a_570_, 1);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v_a_574_);
v___x_576_ = v___x_572_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
else
{
lean_object* v_a_578_; 
lean_del_object(v___x_572_);
v_a_578_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v_a_570_, 1);
v_a_564_ = v_a_578_;
goto v___jp_563_;
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec(v_a_551_);
lean_dec_ref(v_d_549_);
v_a_580_ = lean_ctor_get(v___y_569_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___y_569_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___y_569_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___y_569_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___boxed(lean_object* v_upperBound_745_, lean_object* v_mvarCounterSaved_746_, lean_object* v_d_747_, lean_object* v_thm_748_, lean_object* v_a_749_, lean_object* v_b_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_upperBound_745_, v_mvarCounterSaved_746_, v_d_747_, v_thm_748_, v_a_749_, v_b_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v_thm_748_);
lean_dec(v_mvarCounterSaved_746_);
lean_dec(v_upperBound_745_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(lean_object* v_x_762_, lean_object* v_x_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
if (lean_obj_tag(v_x_762_) == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = l_List_reverse___redArg(v_x_763_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
else
{
lean_object* v_head_776_; lean_object* v_tail_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_787_; 
v_head_776_ = lean_ctor_get(v_x_762_, 0);
v_tail_777_ = lean_ctor_get(v_x_762_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_x_762_);
if (v_isSharedCheck_787_ == 0)
{
v___x_779_ = v_x_762_;
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_tail_777_);
lean_inc(v_head_776_);
lean_dec(v_x_762_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_787_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v_a_782_; lean_object* v___x_784_; 
v___x_781_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_head_776_, v___y_770_);
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref(v___x_781_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_x_763_);
lean_ctor_set(v___x_779_, 0, v_a_782_);
v___x_784_ = v___x_779_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_a_782_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_x_763_);
v___x_784_ = v_reuseFailAlloc_786_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
v_x_762_ = v_tail_777_;
v_x_763_ = v___x_784_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1___boxed(lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_x_788_, v_x_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object* v_thm_803_, lean_object* v_e_804_, lean_object* v_d_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_816_; lean_object* v_mctx_817_; lean_object* v_expr_818_; lean_object* v_pattern_819_; lean_object* v_rhs_820_; uint8_t v_perm_821_; uint8_t v___x_822_; lean_object* v___x_823_; 
v___x_816_ = lean_st_ref_get(v___y_812_);
v_mctx_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc_ref(v_mctx_817_);
lean_dec(v___x_816_);
v_expr_818_ = lean_ctor_get(v_thm_803_, 0);
lean_inc_ref(v_expr_818_);
v_pattern_819_ = lean_ctor_get(v_thm_803_, 1);
lean_inc_ref_n(v_pattern_819_, 2);
v_rhs_820_ = lean_ctor_get(v_thm_803_, 2);
lean_inc_ref(v_rhs_820_);
v_perm_821_ = lean_ctor_get_uint8(v_thm_803_, sizeof(void*)*4);
v___x_822_ = 1;
lean_inc_ref(v_e_804_);
v___x_823_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_819_, v_e_804_, v___x_822_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_937_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_937_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_937_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_937_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
if (lean_obj_tag(v_a_824_) == 1)
{
lean_object* v_val_828_; lean_object* v_us_829_; lean_object* v_args_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
lean_del_object(v___x_826_);
v_val_828_ = lean_ctor_get(v_a_824_, 0);
lean_inc(v_val_828_);
lean_dec_ref_known(v_a_824_, 1);
v_us_829_ = lean_ctor_get(v_val_828_, 0);
lean_inc(v_us_829_);
v_args_830_ = lean_ctor_get(v_val_828_, 1);
lean_inc_ref(v_args_830_);
lean_dec(v_val_828_);
v___x_831_ = lean_box(0);
v___x_832_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_us_829_, v___x_831_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v_mvarCounter_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v_mvarCounter_834_ = lean_ctor_get(v_mctx_817_, 3);
lean_inc(v_mvarCounter_834_);
lean_dec_ref(v_mctx_817_);
v___x_835_ = lean_array_get_size(v_args_830_);
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = 0;
v___x_838_ = lean_box(0);
v___x_839_ = lean_box(v___x_837_);
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v_args_830_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_838_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v___x_835_, v_mvarCounter_834_, v_d_805_, v_thm_803_, v___x_836_, v___x_841_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec_ref(v_thm_803_);
lean_dec(v_mvarCounter_834_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_916_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_916_ == 0)
{
v___x_845_ = v___x_842_;
v_isShared_846_ = v_isSharedCheck_916_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_916_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v_fst_847_; 
v_fst_847_ = lean_ctor_get(v_a_843_, 0);
if (lean_obj_tag(v_fst_847_) == 0)
{
lean_object* v_snd_848_; lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v_levelParams_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
lean_del_object(v___x_845_);
v_snd_848_ = lean_ctor_get(v_a_843_, 1);
lean_inc(v_snd_848_);
lean_dec(v_a_843_);
v_fst_849_ = lean_ctor_get(v_snd_848_, 0);
lean_inc(v_fst_849_);
v_snd_850_ = lean_ctor_get(v_snd_848_, 1);
lean_inc(v_snd_850_);
lean_dec(v_snd_848_);
v_levelParams_851_ = lean_ctor_get(v_pattern_819_, 0);
lean_inc(v_levelParams_851_);
lean_inc(v_a_833_);
v___x_852_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(v_expr_818_, v_pattern_819_, v_a_833_, v_fst_849_);
v___x_853_ = l_Lean_Expr_instantiateLevelParams(v_rhs_820_, v_levelParams_851_, v_a_833_);
lean_dec_ref(v_rhs_820_);
v___x_854_ = l_Lean_Meta_Sym_shareCommonInc(v___x_853_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_a_855_, v_fst_849_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_895_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_895_ == 0)
{
v___x_859_ = v___x_856_;
v_isShared_860_ = v_isSharedCheck_895_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_856_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_895_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
size_t v___x_861_; size_t v___x_862_; uint8_t v___x_863_; 
v___x_861_ = lean_ptr_addr(v_e_804_);
v___x_862_ = lean_ptr_addr(v_a_857_);
v___x_863_ = lean_usize_dec_eq(v___x_861_, v___x_862_);
if (v___x_863_ == 0)
{
lean_object* v___x_864_; 
lean_inc(v_a_857_);
v___x_864_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_821_, v_e_804_, v_a_857_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_881_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_881_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_881_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_881_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
uint8_t v___x_875_; 
v___x_875_ = lean_unbox(v_a_865_);
lean_dec(v_a_865_);
if (v___x_875_ == 0)
{
lean_del_object(v___x_859_);
lean_dec(v_a_857_);
lean_dec_ref(v___x_852_);
goto v___jp_869_;
}
else
{
if (v___x_863_ == 0)
{
lean_object* v___x_876_; uint8_t v___x_877_; lean_object* v___x_879_; 
lean_del_object(v___x_867_);
v___x_876_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_876_, 0, v_a_857_);
lean_ctor_set(v___x_876_, 1, v___x_852_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*2, v___x_837_);
v___x_877_ = lean_unbox(v_snd_850_);
lean_dec(v_snd_850_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*2 + 1, v___x_877_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_876_);
v___x_879_ = v___x_859_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_876_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
else
{
lean_del_object(v___x_859_);
lean_dec(v_a_857_);
lean_dec_ref(v___x_852_);
goto v___jp_869_;
}
}
v___jp_869_:
{
uint8_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_873_; 
v___x_870_ = lean_unbox(v_snd_850_);
lean_dec(v_snd_850_);
v___x_871_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_870_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_871_);
v___x_873_ = v___x_867_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_del_object(v___x_859_);
lean_dec(v_a_857_);
lean_dec_ref(v___x_852_);
lean_dec(v_snd_850_);
v_a_882_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_864_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_864_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
else
{
uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
lean_dec(v_a_857_);
lean_dec_ref(v___x_852_);
lean_dec_ref(v_e_804_);
v___x_890_ = lean_unbox(v_snd_850_);
lean_dec(v_snd_850_);
v___x_891_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_890_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_891_);
v___x_893_ = v___x_859_;
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
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v___x_852_);
lean_dec(v_snd_850_);
lean_dec_ref(v_e_804_);
v_a_896_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_856_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_856_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref(v___x_852_);
lean_dec(v_snd_850_);
lean_dec(v_fst_849_);
lean_dec_ref(v_e_804_);
v_a_904_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_854_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_854_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
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
lean_object* v_val_912_; lean_object* v___x_914_; 
lean_inc_ref(v_fst_847_);
lean_dec(v_a_843_);
lean_dec(v_a_833_);
lean_dec_ref(v_rhs_820_);
lean_dec_ref(v_pattern_819_);
lean_dec_ref(v_expr_818_);
lean_dec_ref(v_e_804_);
v_val_912_ = lean_ctor_get(v_fst_847_, 0);
lean_inc(v_val_912_);
lean_dec_ref_known(v_fst_847_, 1);
if (v_isShared_846_ == 0)
{
lean_ctor_set(v___x_845_, 0, v_val_912_);
v___x_914_ = v___x_845_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_val_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v_a_833_);
lean_dec_ref(v_rhs_820_);
lean_dec_ref(v_pattern_819_);
lean_dec_ref(v_expr_818_);
lean_dec_ref(v_e_804_);
v_a_917_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_842_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_842_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_args_830_);
lean_dec_ref(v_rhs_820_);
lean_dec_ref(v_pattern_819_);
lean_dec_ref(v_expr_818_);
lean_dec_ref(v_mctx_817_);
lean_dec_ref(v_d_805_);
lean_dec_ref(v_e_804_);
lean_dec_ref(v_thm_803_);
v_a_925_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_832_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_832_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
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
lean_object* v___x_933_; lean_object* v___x_935_; 
lean_dec(v_a_824_);
lean_dec_ref(v_rhs_820_);
lean_dec_ref(v_pattern_819_);
lean_dec_ref(v_expr_818_);
lean_dec_ref(v_mctx_817_);
lean_dec_ref(v_d_805_);
lean_dec_ref(v_e_804_);
lean_dec_ref(v_thm_803_);
v___x_933_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0));
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_933_);
v___x_935_ = v___x_826_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec_ref(v_rhs_820_);
lean_dec_ref(v_pattern_819_);
lean_dec_ref(v_expr_818_);
lean_dec_ref(v_mctx_817_);
lean_dec_ref(v_d_805_);
lean_dec_ref(v_e_804_);
lean_dec_ref(v_thm_803_);
v_a_938_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_823_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_823_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object* v_thm_946_, lean_object* v_e_947_, lean_object* v_d_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(v_thm_946_, v_e_947_, v_d_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object* v_thm_960_, lean_object* v_e_961_, lean_object* v_d_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v___f_973_; uint8_t v___x_974_; lean_object* v___x_975_; 
v___f_973_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed), 13, 3);
lean_closure_set(v___f_973_, 0, v_thm_960_);
lean_closure_set(v___f_973_, 1, v_e_961_);
lean_closure_set(v___f_973_, 2, v_d_962_);
v___x_974_ = 0;
v___x_975_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(v___f_973_, v___x_974_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object* v_thm_976_, lean_object* v_e_977_, lean_object* v_d_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_thm_976_, v_e_977_, v_d_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
lean_dec(v_a_987_);
lean_dec_ref(v_a_986_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(lean_object* v_mvarId_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_990_, v___y_997_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(lean_object* v_mvarId_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(v_mvarId_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec_ref(v___y_1004_);
lean_dec(v___y_1003_);
lean_dec(v_mvarId_1002_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(lean_object* v_mvarId_1014_, lean_object* v_val_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_1014_, v_val_1015_, v___y_1022_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(lean_object* v_mvarId_1027_, lean_object* v_val_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(v_mvarId_1027_, v_val_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(lean_object* v_upperBound_1040_, lean_object* v_mvarCounterSaved_1041_, lean_object* v_d_1042_, lean_object* v___x_1043_, lean_object* v_thm_1044_, lean_object* v_inst_1045_, lean_object* v_R_1046_, lean_object* v_a_1047_, lean_object* v_b_1048_, lean_object* v_c_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_upperBound_1040_, v_mvarCounterSaved_1041_, v_d_1042_, v_thm_1044_, v_a_1047_, v_b_1048_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_1061_ = _args[0];
lean_object* v_mvarCounterSaved_1062_ = _args[1];
lean_object* v_d_1063_ = _args[2];
lean_object* v___x_1064_ = _args[3];
lean_object* v_thm_1065_ = _args[4];
lean_object* v_inst_1066_ = _args[5];
lean_object* v_R_1067_ = _args[6];
lean_object* v_a_1068_ = _args[7];
lean_object* v_b_1069_ = _args[8];
lean_object* v_c_1070_ = _args[9];
lean_object* v___y_1071_ = _args[10];
lean_object* v___y_1072_ = _args[11];
lean_object* v___y_1073_ = _args[12];
lean_object* v___y_1074_ = _args[13];
lean_object* v___y_1075_ = _args[14];
lean_object* v___y_1076_ = _args[15];
lean_object* v___y_1077_ = _args[16];
lean_object* v___y_1078_ = _args[17];
lean_object* v___y_1079_ = _args[18];
lean_object* v___y_1080_ = _args[19];
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(v_upperBound_1061_, v_mvarCounterSaved_1062_, v_d_1063_, v___x_1064_, v_thm_1065_, v_inst_1066_, v_R_1067_, v_a_1068_, v_b_1069_, v_c_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v_thm_1065_);
lean_dec(v___x_1064_);
lean_dec(v_mvarCounterSaved_1062_);
lean_dec(v_upperBound_1061_);
return v_res_1081_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
uint8_t v_res_1089_; lean_object* v_r_1090_; 
v_res_1089_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(v_00_u03b2_1086_, v_x_1087_, v_x_1088_);
lean_dec(v_x_1088_);
lean_dec_ref(v_x_1087_);
v_r_1090_ = lean_box(v_res_1089_);
return v_r_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(lean_object* v_00_u03b2_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_x_1092_, v_x_1093_, v_x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1096_, lean_object* v_x_1097_, size_t v_x_1098_, lean_object* v_x_1099_){
_start:
{
uint8_t v___x_1100_; 
v___x_1100_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_1097_, v_x_1098_, v_x_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
size_t v_x_49307__boxed_1105_; uint8_t v_res_1106_; lean_object* v_r_1107_; 
v_x_49307__boxed_1105_ = lean_unbox_usize(v_x_1103_);
lean_dec(v_x_1103_);
v_res_1106_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(v_00_u03b2_1101_, v_x_1102_, v_x_49307__boxed_1105_, v_x_1104_);
lean_dec(v_x_1104_);
lean_dec_ref(v_x_1102_);
v_r_1107_ = lean_box(v_res_1106_);
return v_r_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(lean_object* v_00_u03b2_1108_, lean_object* v_x_1109_, size_t v_x_1110_, size_t v_x_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_1109_, v_x_1110_, v_x_1111_, v_x_1112_, v_x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
size_t v_x_49318__boxed_1121_; size_t v_x_49319__boxed_1122_; lean_object* v_res_1123_; 
v_x_49318__boxed_1121_ = lean_unbox_usize(v_x_1117_);
lean_dec(v_x_1117_);
v_x_49319__boxed_1122_ = lean_unbox_usize(v_x_1118_);
lean_dec(v_x_1118_);
v_res_1123_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(v_00_u03b2_1115_, v_x_1116_, v_x_49318__boxed_1121_, v_x_49319__boxed_1122_, v_x_1119_, v_x_1120_);
return v_res_1123_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1124_, lean_object* v_keys_1125_, lean_object* v_vals_1126_, lean_object* v_heq_1127_, lean_object* v_i_1128_, lean_object* v_k_1129_){
_start:
{
uint8_t v___x_1130_; 
v___x_1130_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_keys_1125_, v_i_1128_, v_k_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1131_, lean_object* v_keys_1132_, lean_object* v_vals_1133_, lean_object* v_heq_1134_, lean_object* v_i_1135_, lean_object* v_k_1136_){
_start:
{
uint8_t v_res_1137_; lean_object* v_r_1138_; 
v_res_1137_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(v_00_u03b2_1131_, v_keys_1132_, v_vals_1133_, v_heq_1134_, v_i_1135_, v_k_1136_);
lean_dec(v_k_1136_);
lean_dec_ref(v_vals_1133_);
lean_dec_ref(v_keys_1132_);
v_r_1138_ = lean_box(v_res_1137_);
return v_r_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_1139_, lean_object* v_n_1140_, lean_object* v_k_1141_, lean_object* v_v_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11___redArg(v_n_1140_, v_k_1141_, v_v_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1144_, size_t v_depth_1145_, lean_object* v_keys_1146_, lean_object* v_vals_1147_, lean_object* v_heq_1148_, lean_object* v_i_1149_, lean_object* v_entries_1150_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_depth_1145_, v_keys_1146_, v_vals_1147_, v_i_1149_, v_entries_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1152_, lean_object* v_depth_1153_, lean_object* v_keys_1154_, lean_object* v_vals_1155_, lean_object* v_heq_1156_, lean_object* v_i_1157_, lean_object* v_entries_1158_){
_start:
{
size_t v_depth_boxed_1159_; lean_object* v_res_1160_; 
v_depth_boxed_1159_ = lean_unbox_usize(v_depth_1153_);
lean_dec(v_depth_1153_);
v_res_1160_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(v_00_u03b2_1152_, v_depth_boxed_1159_, v_keys_1154_, v_vals_1155_, v_heq_1156_, v_i_1157_, v_entries_1158_);
lean_dec_ref(v_vals_1155_);
lean_dec_ref(v_keys_1154_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_, lean_object* v_x_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12___redArg(v_x_1162_, v_x_1163_, v_x_1164_, v_x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(lean_object* v_fst_1167_, lean_object* v_d_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v___x_1180_; 
v___x_1180_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1167_, v_x_1169_, v_d_1168_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed(lean_object* v_fst_1181_, lean_object* v_d_1182_, lean_object* v_x_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(v_fst_1181_, v_d_1182_, v_x_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object* v_d_1195_, lean_object* v_e_1196_, lean_object* v_as_1197_, size_t v_sz_1198_, size_t v_i_1199_, lean_object* v_b_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
uint8_t v___y_1212_; lean_object* v___y_1213_; uint8_t v___y_1219_; lean_object* v___y_1220_; uint8_t v___y_1221_; uint8_t v___y_1224_; uint8_t v___y_1225_; lean_object* v___y_1226_; uint8_t v___y_1227_; uint8_t v___y_1229_; lean_object* v___y_1230_; uint8_t v___y_1231_; lean_object* v___y_1235_; uint8_t v___y_1236_; uint8_t v___x_1238_; 
v___x_1238_ = lean_usize_dec_lt(v_i_1199_, v_sz_1198_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref(v_e_1196_);
lean_dec_ref(v_d_1195_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_b_1200_);
return v___x_1239_;
}
else
{
lean_object* v_a_1240_; lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v_snd_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1292_; 
v_a_1240_ = lean_array_uget_borrowed(v_as_1197_, v_i_1199_);
v_fst_1241_ = lean_ctor_get(v_a_1240_, 0);
v_snd_1242_ = lean_ctor_get(v_a_1240_, 1);
v_snd_1243_ = lean_ctor_get(v_b_1200_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_b_1200_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v_b_1200_, 0);
lean_dec(v_unused_1293_);
v___x_1245_ = v_b_1200_;
v_isShared_1246_ = v_isSharedCheck_1292_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_snd_1243_);
lean_dec(v_b_1200_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1292_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1247_; lean_object* v___y_1249_; uint8_t v_done_1250_; uint8_t v___y_1251_; lean_object* v_result_1261_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1247_ = lean_box(0);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_nat_dec_eq(v_snd_1242_, v___x_1269_);
if (v___x_1270_ == 0)
{
lean_object* v___f_1271_; lean_object* v___x_1272_; 
lean_inc_ref(v_d_1195_);
lean_inc(v_fst_1241_);
v___f_1271_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1271_, 0, v_fst_1241_);
lean_closure_set(v___f_1271_, 1, v_d_1195_);
lean_inc_ref(v_e_1196_);
v___x_1272_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_1196_, v_snd_1242_, v___f_1271_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v_result_1261_ = v_a_1273_;
goto v___jp_1260_;
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_del_object(v___x_1245_);
lean_dec(v_snd_1243_);
lean_dec_ref(v_e_1196_);
lean_dec_ref(v_d_1195_);
v_a_1274_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1272_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1272_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
else
{
lean_object* v___x_1282_; 
lean_inc_ref(v_d_1195_);
lean_inc_ref(v_e_1196_);
lean_inc(v_fst_1241_);
v___x_1282_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1241_, v_e_1196_, v_d_1195_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
if (lean_obj_tag(v___x_1282_) == 0)
{
lean_object* v_a_1283_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_a_1283_);
lean_dec_ref_known(v___x_1282_, 1);
v_result_1261_ = v_a_1283_;
goto v___jp_1260_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_del_object(v___x_1245_);
lean_dec(v_snd_1243_);
lean_dec_ref(v_e_1196_);
lean_dec_ref(v_d_1195_);
v_a_1284_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1282_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1282_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
v___jp_1248_:
{
if (v_done_1250_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
lean_dec_ref(v___y_1249_);
v___x_1252_ = lean_box(v___y_1251_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1252_);
lean_ctor_set(v___x_1245_, 0, v___x_1247_);
v___x_1254_ = v___x_1245_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1247_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
size_t v___x_1255_; size_t v___x_1256_; 
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_add(v_i_1199_, v___x_1255_);
v_i_1199_ = v___x_1256_;
v_b_1200_ = v___x_1254_;
goto _start;
}
}
else
{
uint8_t v___x_1259_; 
lean_del_object(v___x_1245_);
lean_dec_ref(v_e_1196_);
lean_dec_ref(v_d_1195_);
v___x_1259_ = 0;
v___y_1229_ = v___y_1251_;
v___y_1230_ = v___y_1249_;
v___y_1231_ = v___x_1259_;
goto v___jp_1228_;
}
}
v___jp_1260_:
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_unbox(v_snd_1243_);
if (v___x_1262_ == 0)
{
lean_dec(v_snd_1243_);
if (lean_obj_tag(v_result_1261_) == 0)
{
uint8_t v_done_1263_; uint8_t v_contextDependent_1264_; 
v_done_1263_ = lean_ctor_get_uint8(v_result_1261_, 0);
v_contextDependent_1264_ = lean_ctor_get_uint8(v_result_1261_, 1);
v___y_1249_ = v_result_1261_;
v_done_1250_ = v_done_1263_;
v___y_1251_ = v_contextDependent_1264_;
goto v___jp_1248_;
}
else
{
uint8_t v_contextDependent_1265_; 
lean_del_object(v___x_1245_);
lean_dec_ref(v_e_1196_);
lean_dec_ref(v_d_1195_);
v_contextDependent_1265_ = lean_ctor_get_uint8(v_result_1261_, sizeof(void*)*2 + 1);
v___y_1235_ = v_result_1261_;
v___y_1236_ = v_contextDependent_1265_;
goto v___jp_1234_;
}
}
else
{
if (lean_obj_tag(v_result_1261_) == 0)
{
uint8_t v_done_1266_; uint8_t v___x_1267_; 
v_done_1266_ = lean_ctor_get_uint8(v_result_1261_, 0);
v___x_1267_ = lean_unbox(v_snd_1243_);
lean_dec(v_snd_1243_);
v___y_1249_ = v_result_1261_;
v_done_1250_ = v_done_1266_;
v___y_1251_ = v___x_1267_;
goto v___jp_1248_;
}
else
{
uint8_t v___x_1268_; 
lean_del_object(v___x_1245_);
lean_dec_ref(v_e_1196_);
lean_dec_ref(v_d_1195_);
v___x_1268_ = lean_unbox(v_snd_1243_);
lean_dec(v_snd_1243_);
v___y_1235_ = v_result_1261_;
v___y_1236_ = v___x_1268_;
goto v___jp_1234_;
}
}
}
}
}
v___jp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___y_1213_);
v___x_1215_ = lean_box(v___y_1212_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1214_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
return v___x_1217_;
}
v___jp_1218_:
{
if (v___y_1221_ == 0)
{
v___y_1212_ = v___y_1219_;
v___y_1213_ = v___y_1220_;
goto v___jp_1211_;
}
else
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1220_);
v___y_1212_ = v___y_1219_;
v___y_1213_ = v___x_1222_;
goto v___jp_1211_;
}
}
v___jp_1223_:
{
if (v___y_1227_ == 0)
{
v___y_1219_ = v___y_1224_;
v___y_1220_ = v___y_1226_;
v___y_1221_ = v___y_1224_;
goto v___jp_1218_;
}
else
{
v___y_1219_ = v___y_1224_;
v___y_1220_ = v___y_1226_;
v___y_1221_ = v___y_1225_;
goto v___jp_1218_;
}
}
v___jp_1228_:
{
if (v___y_1229_ == 0)
{
v___y_1212_ = v___y_1229_;
v___y_1213_ = v___y_1230_;
goto v___jp_1211_;
}
else
{
if (lean_obj_tag(v___y_1230_) == 0)
{
uint8_t v_contextDependent_1232_; 
v_contextDependent_1232_ = lean_ctor_get_uint8(v___y_1230_, 1);
v___y_1224_ = v___y_1229_;
v___y_1225_ = v___y_1231_;
v___y_1226_ = v___y_1230_;
v___y_1227_ = v_contextDependent_1232_;
goto v___jp_1223_;
}
else
{
uint8_t v_contextDependent_1233_; 
v_contextDependent_1233_ = lean_ctor_get_uint8(v___y_1230_, sizeof(void*)*2 + 1);
v___y_1224_ = v___y_1229_;
v___y_1225_ = v___y_1231_;
v___y_1226_ = v___y_1230_;
v___y_1227_ = v_contextDependent_1233_;
goto v___jp_1223_;
}
}
}
v___jp_1234_:
{
uint8_t v___x_1237_; 
v___x_1237_ = 0;
v___y_1229_ = v___y_1236_;
v___y_1230_ = v___y_1235_;
v___y_1231_ = v___x_1237_;
goto v___jp_1228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object* v_d_1294_, lean_object* v_e_1295_, lean_object* v_as_1296_, lean_object* v_sz_1297_, lean_object* v_i_1298_, lean_object* v_b_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
size_t v_sz_boxed_1310_; size_t v_i_boxed_1311_; lean_object* v_res_1312_; 
v_sz_boxed_1310_ = lean_unbox_usize(v_sz_1297_);
lean_dec(v_sz_1297_);
v_i_boxed_1311_ = lean_unbox_usize(v_i_1298_);
lean_dec(v_i_1298_);
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1294_, v_e_1295_, v_as_1296_, v_sz_boxed_1310_, v_i_boxed_1311_, v_b_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v_as_1296_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object* v_thms_1317_, lean_object* v_d_1318_, lean_object* v_e_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v___x_1330_; lean_object* v_mctx_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; size_t v_sz_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v___x_1330_ = lean_st_ref_get(v_a_1326_);
v_mctx_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc_ref(v_mctx_1331_);
lean_dec(v___x_1330_);
v___x_1332_ = l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(v_thms_1317_, v_mctx_1331_, v_e_1319_);
lean_dec_ref(v_mctx_1331_);
v___x_1333_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0));
v_sz_1334_ = lean_array_size(v___x_1332_);
v___x_1335_ = ((size_t)0ULL);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1318_, v_e_1319_, v___x_1332_, v_sz_1334_, v___x_1335_, v___x_1333_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
lean_dec_ref(v___x_1332_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1352_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1339_ = v___x_1336_;
v_isShared_1340_ = v_isSharedCheck_1352_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1336_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1352_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v_fst_1341_; 
v_fst_1341_ = lean_ctor_get(v_a_1337_, 0);
if (lean_obj_tag(v_fst_1341_) == 0)
{
lean_object* v_snd_1342_; uint8_t v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v_snd_1342_ = lean_ctor_get(v_a_1337_, 1);
lean_inc(v_snd_1342_);
lean_dec(v_a_1337_);
v___x_1343_ = lean_unbox(v_snd_1342_);
lean_dec(v_snd_1342_);
v___x_1344_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1343_);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v___x_1344_);
v___x_1346_ = v___x_1339_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
else
{
lean_object* v_val_1348_; lean_object* v___x_1350_; 
lean_inc_ref(v_fst_1341_);
lean_dec(v_a_1337_);
v_val_1348_ = lean_ctor_get(v_fst_1341_, 0);
lean_inc(v_val_1348_);
lean_dec_ref_known(v_fst_1341_, 1);
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 0, v_val_1348_);
v___x_1350_ = v___x_1339_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_val_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_a_1353_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1355_ = v___x_1336_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1336_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_a_1353_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object* v_thms_1361_, lean_object* v_d_1362_, lean_object* v_e_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_thms_1361_, v_d_1362_, v_e_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_thms_1361_);
return v_res_1374_;
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
