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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
size_t v_x_43909__boxed_271_; uint8_t v_res_272_; lean_object* v_r_273_; 
v_x_43909__boxed_271_ = lean_unbox_usize(v_x_269_);
lean_dec(v_x_269_);
v_res_272_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_268_, v_x_43909__boxed_271_, v_x_270_);
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
size_t v_x_44052__boxed_435_; size_t v_x_44053__boxed_436_; lean_object* v_res_437_; 
v_x_44052__boxed_435_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_x_44053__boxed_436_ = lean_unbox_usize(v_x_432_);
lean_dec(v_x_432_);
v_res_437_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_430_, v_x_44052__boxed_435_, v_x_44053__boxed_436_, v_x_433_, v_x_434_);
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
lean_object* v___x_449_; lean_object* v_mctx_450_; lean_object* v_cache_451_; lean_object* v_zetaDeltaFVarIds_452_; lean_object* v_postponed_453_; lean_object* v_diag_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_483_; 
v___x_449_ = lean_st_ref_take(v___y_447_);
v_mctx_450_ = lean_ctor_get(v___x_449_, 0);
v_cache_451_ = lean_ctor_get(v___x_449_, 1);
v_zetaDeltaFVarIds_452_ = lean_ctor_get(v___x_449_, 2);
v_postponed_453_ = lean_ctor_get(v___x_449_, 3);
v_diag_454_ = lean_ctor_get(v___x_449_, 4);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_483_ == 0)
{
v___x_456_ = v___x_449_;
v_isShared_457_ = v_isSharedCheck_483_;
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
v_isShared_457_ = v_isSharedCheck_483_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v_depth_458_; lean_object* v_levelAssignDepth_459_; lean_object* v_lmvarCounter_460_; lean_object* v_mvarCounter_461_; lean_object* v_lDecls_462_; lean_object* v_decls_463_; lean_object* v_userNames_464_; lean_object* v_lAssignment_465_; lean_object* v_eAssignment_466_; lean_object* v_dAssignment_467_; lean_object* v_instanceTypedMVars_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_482_; 
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
v_instanceTypedMVars_468_ = lean_ctor_get(v_mctx_450_, 10);
v_isSharedCheck_482_ = !lean_is_exclusive(v_mctx_450_);
if (v_isSharedCheck_482_ == 0)
{
v___x_470_ = v_mctx_450_;
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_instanceTypedMVars_468_);
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
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_eAssignment_466_, v_mvarId_445_, v_val_446_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 8, v___x_472_);
v___x_474_ = v___x_470_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_depth_458_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_levelAssignDepth_459_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_lmvarCounter_460_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_mvarCounter_461_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_lDecls_462_);
lean_ctor_set(v_reuseFailAlloc_481_, 5, v_decls_463_);
lean_ctor_set(v_reuseFailAlloc_481_, 6, v_userNames_464_);
lean_ctor_set(v_reuseFailAlloc_481_, 7, v_lAssignment_465_);
lean_ctor_set(v_reuseFailAlloc_481_, 8, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_481_, 9, v_dAssignment_467_);
lean_ctor_set(v_reuseFailAlloc_481_, 10, v_instanceTypedMVars_468_);
v___x_474_ = v_reuseFailAlloc_481_;
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
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_cache_451_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_zetaDeltaFVarIds_452_);
lean_ctor_set(v_reuseFailAlloc_480_, 3, v_postponed_453_);
lean_ctor_set(v_reuseFailAlloc_480_, 4, v_diag_454_);
v___x_476_ = v_reuseFailAlloc_480_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_st_ref_put(v___y_447_, v___x_476_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(lean_object* v_mvarId_484_, lean_object* v_val_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_484_, v_val_485_, v___y_486_);
lean_dec(v___y_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(lean_object* v_mvarId_489_, lean_object* v_fst_490_, lean_object* v_a_491_, uint8_t v___y_492_, lean_object* v___x_493_, lean_object* v_val_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; 
lean_inc_ref(v_val_494_);
v___x_505_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_489_, v_val_494_, v___y_501_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_517_; 
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v___x_505_, 0);
lean_dec(v_unused_518_);
v___x_507_ = v___x_505_;
v_isShared_508_ = v_isSharedCheck_517_;
goto v_resetjp_506_;
}
else
{
lean_dec(v___x_505_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_517_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_509_ = lean_array_fset(v_fst_490_, v_a_491_, v_val_494_);
v___x_510_ = lean_box(v___y_492_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_493_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_513_);
v___x_515_ = v___x_507_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec_ref(v_val_494_);
lean_dec(v___x_493_);
lean_dec(v_fst_490_);
v_a_519_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_505_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_505_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed(lean_object* v_mvarId_527_, lean_object* v_fst_528_, lean_object* v_a_529_, lean_object* v___y_530_, lean_object* v___x_531_, lean_object* v_val_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
uint8_t v___y_44262__boxed_543_; lean_object* v_res_544_; 
v___y_44262__boxed_543_ = lean_unbox(v___y_530_);
v_res_544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_527_, v_fst_528_, v_a_529_, v___y_44262__boxed_543_, v___x_531_, v_val_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec(v_a_529_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(lean_object* v_upperBound_545_, lean_object* v_mvarCounterSaved_546_, lean_object* v_d_547_, lean_object* v_thm_548_, lean_object* v_a_549_, lean_object* v_b_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_a_562_; lean_object* v___y_567_; uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_lt(v_a_549_, v_upperBound_545_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_b_550_);
return v___x_587_;
}
else
{
lean_object* v_snd_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_741_; 
v_snd_588_ = lean_ctor_get(v_b_550_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_b_550_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v_b_550_, 0);
lean_dec(v_unused_742_);
v___x_590_ = v_b_550_;
v_isShared_591_ = v_isSharedCheck_741_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snd_588_);
lean_dec(v_b_550_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_741_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v_fst_592_; lean_object* v_snd_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_740_; 
v_fst_592_ = lean_ctor_get(v_snd_588_, 0);
v_snd_593_ = lean_ctor_get(v_snd_588_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_snd_588_);
if (v_isSharedCheck_740_ == 0)
{
v___x_595_ = v_snd_588_;
v_isShared_596_ = v_isSharedCheck_740_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_snd_593_);
lean_inc(v_fst_592_);
lean_dec(v_snd_588_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_740_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = lean_box(0);
v___x_598_ = lean_array_fget_borrowed(v_fst_592_, v_a_549_);
if (lean_obj_tag(v___x_598_) == 2)
{
lean_object* v_mvarId_599_; lean_object* v___x_600_; 
v_mvarId_599_ = lean_ctor_get(v___x_598_, 0);
v___x_600_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_599_, v___y_557_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; uint8_t v___x_602_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_602_ = lean_unbox(v_a_601_);
lean_dec(v_a_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
lean_inc(v_mvarId_599_);
v___x_603_ = l_Lean_MVarId_getDecl(v_mvarId_599_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v_type_605_; lean_object* v_index_606_; uint8_t v___x_607_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref_known(v___x_603_, 1);
v_type_605_ = lean_ctor_get(v_a_604_, 2);
lean_inc_ref(v_type_605_);
v_index_606_ = lean_ctor_get(v_a_604_, 6);
lean_inc(v_index_606_);
lean_dec(v_a_604_);
v___x_607_ = lean_nat_dec_le(v_mvarCounterSaved_546_, v_index_606_);
lean_dec(v_index_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v_type_605_);
if (v_isShared_596_ == 0)
{
v___x_609_ = v___x_595_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_fst_592_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_snd_593_);
v___x_609_ = v_reuseFailAlloc_613_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_611_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_609_);
lean_ctor_set(v___x_590_, 0, v___x_597_);
v___x_611_ = v___x_590_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
v_a_562_ = v___x_611_;
goto v___jp_561_;
}
}
}
else
{
lean_object* v___x_614_; 
lean_inc_ref(v_d_547_);
lean_inc(v___y_559_);
lean_inc_ref(v___y_558_);
lean_inc(v___y_557_);
lean_inc_ref(v___y_556_);
lean_inc(v___y_555_);
lean_inc_ref(v___y_554_);
lean_inc(v___y_553_);
lean_inc_ref(v___y_552_);
lean_inc(v___y_551_);
v___x_614_ = lean_apply_11(v_d_547_, v_type_605_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, lean_box(0));
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_674_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_674_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_674_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_674_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint8_t v___y_620_; 
if (lean_obj_tag(v_a_615_) == 0)
{
uint8_t v___x_633_; 
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v___x_633_ = lean_unbox(v_snd_593_);
lean_dec(v_snd_593_);
if (v___x_633_ == 0)
{
uint8_t v_contextDependent_634_; 
v_contextDependent_634_ = lean_ctor_get_uint8(v_a_615_, 0);
lean_dec_ref_known(v_a_615_, 0);
v___y_620_ = v_contextDependent_634_;
goto v___jp_619_;
}
else
{
lean_dec_ref_known(v_a_615_, 0);
v___y_620_ = v___x_607_;
goto v___jp_619_;
}
}
else
{
lean_object* v_proof_635_; uint8_t v_contextDependent_636_; uint8_t v___y_638_; uint8_t v___x_673_; 
lean_inc(v_mvarId_599_);
lean_del_object(v___x_617_);
lean_del_object(v___x_595_);
lean_del_object(v___x_590_);
v_proof_635_ = lean_ctor_get(v_a_615_, 0);
lean_inc_ref(v_proof_635_);
v_contextDependent_636_ = lean_ctor_get_uint8(v_a_615_, sizeof(void*)*1);
lean_dec_ref_known(v_a_615_, 1);
v___x_673_ = lean_unbox(v_snd_593_);
lean_dec(v_snd_593_);
if (v___x_673_ == 0)
{
v___y_638_ = v_contextDependent_636_;
goto v___jp_637_;
}
else
{
v___y_638_ = v___x_607_;
goto v___jp_637_;
}
v___jp_637_:
{
lean_object* v_rhsVarMask_639_; uint8_t v___x_640_; 
v_rhsVarMask_639_ = lean_ctor_get(v_thm_548_, 3);
v___x_640_ = l_Nat_testBit(v_rhsVarMask_639_, v_a_549_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_proof_635_, v___y_557_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_643_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
lean_dec_ref_known(v___x_641_, 1);
v___x_643_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_599_, v_fst_592_, v_a_549_, v___y_638_, v___x_597_, v_a_642_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
v___y_567_ = v___x_643_;
goto v___jp_566_;
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec(v_mvarId_599_);
lean_dec(v_fst_592_);
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v_a_644_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_641_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_641_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_proof_635_, v___y_557_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = l_Lean_Meta_Sym_shareCommon(v_a_653_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v___x_656_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_599_, v_fst_592_, v_a_549_, v___y_638_, v___x_597_, v_a_655_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
v___y_567_ = v___x_656_;
goto v___jp_566_;
}
else
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_664_; 
lean_dec(v_mvarId_599_);
lean_dec(v_fst_592_);
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v_a_657_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_664_ == 0)
{
v___x_659_ = v___x_654_;
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_654_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_664_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_662_; 
if (v_isShared_660_ == 0)
{
v___x_662_ = v___x_659_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_a_657_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_mvarId_599_);
lean_dec(v_fst_592_);
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v_a_665_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_652_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_652_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
v___jp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_621_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_620_);
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
v___x_623_ = lean_box(v___y_620_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v___x_623_);
v___x_625_ = v___x_595_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_fst_592_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_623_);
v___x_625_ = v_reuseFailAlloc_632_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_625_);
lean_ctor_set(v___x_590_, 0, v___x_622_);
v___x_627_ = v___x_590_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_625_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_627_);
v___x_629_ = v___x_617_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
lean_dec(v_fst_592_);
lean_del_object(v___x_590_);
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v_a_675_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_614_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_614_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
lean_dec(v_fst_592_);
lean_del_object(v___x_590_);
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v_a_683_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_603_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_603_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
else
{
lean_object* v___x_691_; 
lean_inc_ref(v___x_598_);
v___x_691_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_598_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_693_; lean_object* v___x_695_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
v___x_693_ = lean_array_fset(v_fst_592_, v_a_549_, v_a_692_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_693_);
v___x_695_ = v___x_595_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_snd_593_);
v___x_695_ = v_reuseFailAlloc_699_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_697_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_695_);
lean_ctor_set(v___x_590_, 0, v___x_597_);
v___x_697_ = v___x_590_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
v_a_562_ = v___x_697_;
goto v___jp_561_;
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
lean_dec(v_fst_592_);
lean_del_object(v___x_590_);
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v_a_700_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_691_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_691_);
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
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
lean_dec(v_fst_592_);
lean_del_object(v___x_590_);
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v_a_708_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___x_600_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_600_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
uint8_t v___x_716_; 
v___x_716_ = l_Lean_Expr_hasMVar(v___x_598_);
if (v___x_716_ == 0)
{
lean_object* v___x_718_; 
if (v_isShared_596_ == 0)
{
v___x_718_ = v___x_595_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_fst_592_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_snd_593_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_718_);
lean_ctor_set(v___x_590_, 0, v___x_597_);
v___x_720_ = v___x_590_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
v_a_562_ = v___x_720_;
goto v___jp_561_;
}
}
}
else
{
lean_object* v___x_723_; 
lean_inc(v___x_598_);
v___x_723_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_598_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v___x_725_ = lean_array_fset(v_fst_592_, v_a_549_, v_a_724_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_725_);
v___x_727_ = v___x_595_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_snd_593_);
v___x_727_ = v_reuseFailAlloc_731_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_729_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_727_);
lean_ctor_set(v___x_590_, 0, v___x_597_);
v___x_729_ = v___x_590_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
v_a_562_ = v___x_729_;
goto v___jp_561_;
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_del_object(v___x_595_);
lean_dec(v_snd_593_);
lean_dec(v_fst_592_);
lean_del_object(v___x_590_);
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v_a_732_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_723_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_723_);
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
}
}
}
}
v___jp_561_:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = lean_unsigned_to_nat(1u);
v___x_564_ = lean_nat_add(v_a_549_, v___x_563_);
lean_dec(v_a_549_);
v_a_549_ = v___x_564_;
v_b_550_ = v_a_562_;
goto _start;
}
v___jp_566_:
{
if (lean_obj_tag(v___y_567_) == 0)
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_577_; 
v_a_568_ = lean_ctor_get(v___y_567_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___y_567_);
if (v_isSharedCheck_577_ == 0)
{
v___x_570_ = v___y_567_;
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___y_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_577_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
if (lean_obj_tag(v_a_568_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; 
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v_a_572_ = lean_ctor_get(v_a_568_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v_a_568_, 1);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 0, v_a_572_);
v___x_574_ = v___x_570_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
else
{
lean_object* v_a_576_; 
lean_del_object(v___x_570_);
v_a_576_ = lean_ctor_get(v_a_568_, 0);
lean_inc(v_a_576_);
lean_dec_ref_known(v_a_568_, 1);
v_a_562_ = v_a_576_;
goto v___jp_561_;
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec(v_a_549_);
lean_dec_ref(v_d_547_);
v_a_578_ = lean_ctor_get(v___y_567_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___y_567_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___y_567_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___y_567_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___boxed(lean_object* v_upperBound_743_, lean_object* v_mvarCounterSaved_744_, lean_object* v_d_745_, lean_object* v_thm_746_, lean_object* v_a_747_, lean_object* v_b_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_upperBound_743_, v_mvarCounterSaved_744_, v_d_745_, v_thm_746_, v_a_747_, v_b_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v_thm_746_);
lean_dec(v_mvarCounterSaved_744_);
lean_dec(v_upperBound_743_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = l_List_reverse___redArg(v_x_761_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
else
{
lean_object* v_head_774_; lean_object* v_tail_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_785_; 
v_head_774_ = lean_ctor_get(v_x_760_, 0);
v_tail_775_ = lean_ctor_get(v_x_760_, 1);
v_isSharedCheck_785_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_785_ == 0)
{
v___x_777_ = v_x_760_;
v_isShared_778_ = v_isSharedCheck_785_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_tail_775_);
lean_inc(v_head_774_);
lean_dec(v_x_760_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_785_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v___x_782_; 
v___x_779_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_head_774_, v___y_768_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref(v___x_779_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v_x_761_);
lean_ctor_set(v___x_777_, 0, v_a_780_);
v___x_782_ = v___x_777_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_780_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_x_761_);
v___x_782_ = v_reuseFailAlloc_784_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
v_x_760_ = v_tail_775_;
v_x_761_ = v___x_782_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1___boxed(lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_x_786_, v_x_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object* v_thm_801_, lean_object* v_e_802_, lean_object* v_d_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; lean_object* v_mctx_815_; lean_object* v_expr_816_; lean_object* v_pattern_817_; lean_object* v_rhs_818_; uint8_t v_perm_819_; uint8_t v___x_820_; lean_object* v___x_821_; 
v___x_814_ = lean_st_ref_get(v___y_810_);
v_mctx_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc_ref(v_mctx_815_);
lean_dec(v___x_814_);
v_expr_816_ = lean_ctor_get(v_thm_801_, 0);
lean_inc_ref(v_expr_816_);
v_pattern_817_ = lean_ctor_get(v_thm_801_, 1);
lean_inc_ref_n(v_pattern_817_, 2);
v_rhs_818_ = lean_ctor_get(v_thm_801_, 2);
lean_inc_ref(v_rhs_818_);
v_perm_819_ = lean_ctor_get_uint8(v_thm_801_, sizeof(void*)*4);
v___x_820_ = 1;
lean_inc_ref(v_e_802_);
v___x_821_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_817_, v_e_802_, v___x_820_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_934_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_934_ == 0)
{
v___x_824_ = v___x_821_;
v_isShared_825_ = v_isSharedCheck_934_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_821_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_934_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
if (lean_obj_tag(v_a_822_) == 1)
{
lean_object* v_val_826_; lean_object* v_us_827_; lean_object* v_args_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_del_object(v___x_824_);
v_val_826_ = lean_ctor_get(v_a_822_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v_a_822_, 1);
v_us_827_ = lean_ctor_get(v_val_826_, 0);
lean_inc(v_us_827_);
v_args_828_ = lean_ctor_get(v_val_826_, 1);
lean_inc_ref(v_args_828_);
lean_dec(v_val_826_);
v___x_829_ = lean_box(0);
v___x_830_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_us_827_, v___x_829_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v_a_831_; lean_object* v_mvarCounter_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref_known(v___x_830_, 1);
v_mvarCounter_832_ = lean_ctor_get(v_mctx_815_, 3);
lean_inc(v_mvarCounter_832_);
lean_dec_ref(v_mctx_815_);
v___x_833_ = lean_array_get_size(v_args_828_);
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = 0;
v___x_836_ = lean_box(0);
v___x_837_ = lean_box(v___x_835_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v_args_828_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_836_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v___x_833_, v_mvarCounter_832_, v_d_803_, v_thm_801_, v___x_834_, v___x_839_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
lean_dec_ref(v_thm_801_);
lean_dec(v_mvarCounter_832_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_913_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_913_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_913_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_913_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v_fst_845_; 
v_fst_845_ = lean_ctor_get(v_a_841_, 0);
if (lean_obj_tag(v_fst_845_) == 0)
{
lean_object* v_snd_846_; lean_object* v_fst_847_; lean_object* v_snd_848_; lean_object* v_levelParams_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_del_object(v___x_843_);
v_snd_846_ = lean_ctor_get(v_a_841_, 1);
lean_inc(v_snd_846_);
lean_dec(v_a_841_);
v_fst_847_ = lean_ctor_get(v_snd_846_, 0);
lean_inc(v_fst_847_);
v_snd_848_ = lean_ctor_get(v_snd_846_, 1);
lean_inc(v_snd_848_);
lean_dec(v_snd_846_);
v_levelParams_849_ = lean_ctor_get(v_pattern_817_, 0);
lean_inc(v_levelParams_849_);
lean_inc(v_a_831_);
v___x_850_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(v_expr_816_, v_pattern_817_, v_a_831_, v_fst_847_);
v___x_851_ = l_Lean_Expr_instantiateLevelParams(v_rhs_818_, v_levelParams_849_, v_a_831_);
lean_dec_ref(v_rhs_818_);
v___x_852_ = l_Lean_Meta_Sym_shareCommonInc(v___x_851_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_a_853_, v_fst_847_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_892_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_892_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_892_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_892_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
size_t v___x_859_; size_t v___x_860_; uint8_t v___x_861_; 
v___x_859_ = lean_ptr_addr(v_e_802_);
v___x_860_ = lean_ptr_addr(v_a_855_);
v___x_861_ = lean_usize_dec_eq(v___x_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
lean_del_object(v___x_857_);
lean_inc(v_a_855_);
v___x_862_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_819_, v_e_802_, v_a_855_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_878_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_878_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_878_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_878_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
uint8_t v___x_867_; 
v___x_867_ = lean_unbox(v_a_863_);
lean_dec(v_a_863_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
lean_dec(v_a_855_);
lean_dec_ref(v___x_850_);
v___x_868_ = lean_unbox(v_snd_848_);
lean_dec(v_snd_848_);
v___x_869_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_868_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_869_);
v___x_871_ = v___x_865_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
else
{
lean_object* v___x_873_; uint8_t v___x_874_; lean_object* v___x_876_; 
v___x_873_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_873_, 0, v_a_855_);
lean_ctor_set(v___x_873_, 1, v___x_850_);
lean_ctor_set_uint8(v___x_873_, sizeof(void*)*2, v___x_835_);
v___x_874_ = lean_unbox(v_snd_848_);
lean_dec(v_snd_848_);
lean_ctor_set_uint8(v___x_873_, sizeof(void*)*2 + 1, v___x_874_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_873_);
v___x_876_ = v___x_865_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_873_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
lean_dec(v_a_855_);
lean_dec_ref(v___x_850_);
lean_dec(v_snd_848_);
v_a_879_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_862_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_862_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
else
{
uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
lean_dec(v_a_855_);
lean_dec_ref(v___x_850_);
lean_dec_ref(v_e_802_);
v___x_887_ = lean_unbox(v_snd_848_);
lean_dec(v_snd_848_);
v___x_888_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_887_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_888_);
v___x_890_ = v___x_857_;
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
}
}
else
{
lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec_ref(v___x_850_);
lean_dec(v_snd_848_);
lean_dec_ref(v_e_802_);
v_a_893_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_854_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_854_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v___x_850_);
lean_dec(v_snd_848_);
lean_dec(v_fst_847_);
lean_dec_ref(v_e_802_);
v_a_901_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_852_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_852_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v_val_909_; lean_object* v___x_911_; 
lean_inc_ref(v_fst_845_);
lean_dec(v_a_841_);
lean_dec(v_a_831_);
lean_dec_ref(v_rhs_818_);
lean_dec_ref(v_pattern_817_);
lean_dec_ref(v_expr_816_);
lean_dec_ref(v_e_802_);
v_val_909_ = lean_ctor_get(v_fst_845_, 0);
lean_inc(v_val_909_);
lean_dec_ref_known(v_fst_845_, 1);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v_val_909_);
v___x_911_ = v___x_843_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_val_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_a_831_);
lean_dec_ref(v_rhs_818_);
lean_dec_ref(v_pattern_817_);
lean_dec_ref(v_expr_816_);
lean_dec_ref(v_e_802_);
v_a_914_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_840_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_840_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec_ref(v_args_828_);
lean_dec_ref(v_rhs_818_);
lean_dec_ref(v_pattern_817_);
lean_dec_ref(v_expr_816_);
lean_dec_ref(v_mctx_815_);
lean_dec_ref(v_d_803_);
lean_dec_ref(v_e_802_);
lean_dec_ref(v_thm_801_);
v_a_922_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_830_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_830_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v___x_930_; lean_object* v___x_932_; 
lean_dec(v_a_822_);
lean_dec_ref(v_rhs_818_);
lean_dec_ref(v_pattern_817_);
lean_dec_ref(v_expr_816_);
lean_dec_ref(v_mctx_815_);
lean_dec_ref(v_d_803_);
lean_dec_ref(v_e_802_);
lean_dec_ref(v_thm_801_);
v___x_930_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0));
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_930_);
v___x_932_ = v___x_824_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec_ref(v_rhs_818_);
lean_dec_ref(v_pattern_817_);
lean_dec_ref(v_expr_816_);
lean_dec_ref(v_mctx_815_);
lean_dec_ref(v_d_803_);
lean_dec_ref(v_e_802_);
lean_dec_ref(v_thm_801_);
v_a_935_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_821_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_821_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object* v_thm_943_, lean_object* v_e_944_, lean_object* v_d_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(v_thm_943_, v_e_944_, v_d_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object* v_thm_957_, lean_object* v_e_958_, lean_object* v_d_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v___f_970_; uint8_t v___x_971_; lean_object* v___x_972_; 
v___f_970_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed), 13, 3);
lean_closure_set(v___f_970_, 0, v_thm_957_);
lean_closure_set(v___f_970_, 1, v_e_958_);
lean_closure_set(v___f_970_, 2, v_d_959_);
v___x_971_ = 0;
v___x_972_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(v___f_970_, v___x_971_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object* v_thm_973_, lean_object* v_e_974_, lean_object* v_d_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_thm_973_, v_e_974_, v_d_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(lean_object* v_mvarId_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_987_, v___y_994_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(lean_object* v_mvarId_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(v_mvarId_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec(v_mvarId_999_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(lean_object* v_mvarId_1011_, lean_object* v_val_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_1011_, v_val_1012_, v___y_1019_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(lean_object* v_mvarId_1024_, lean_object* v_val_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(v_mvarId_1024_, v_val_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(lean_object* v_upperBound_1037_, lean_object* v_mvarCounterSaved_1038_, lean_object* v_d_1039_, lean_object* v___x_1040_, lean_object* v_thm_1041_, lean_object* v_inst_1042_, lean_object* v_R_1043_, lean_object* v_a_1044_, lean_object* v_b_1045_, lean_object* v_c_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_upperBound_1037_, v_mvarCounterSaved_1038_, v_d_1039_, v_thm_1041_, v_a_1044_, v_b_1045_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_1058_ = _args[0];
lean_object* v_mvarCounterSaved_1059_ = _args[1];
lean_object* v_d_1060_ = _args[2];
lean_object* v___x_1061_ = _args[3];
lean_object* v_thm_1062_ = _args[4];
lean_object* v_inst_1063_ = _args[5];
lean_object* v_R_1064_ = _args[6];
lean_object* v_a_1065_ = _args[7];
lean_object* v_b_1066_ = _args[8];
lean_object* v_c_1067_ = _args[9];
lean_object* v___y_1068_ = _args[10];
lean_object* v___y_1069_ = _args[11];
lean_object* v___y_1070_ = _args[12];
lean_object* v___y_1071_ = _args[13];
lean_object* v___y_1072_ = _args[14];
lean_object* v___y_1073_ = _args[15];
lean_object* v___y_1074_ = _args[16];
lean_object* v___y_1075_ = _args[17];
lean_object* v___y_1076_ = _args[18];
lean_object* v___y_1077_ = _args[19];
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(v_upperBound_1058_, v_mvarCounterSaved_1059_, v_d_1060_, v___x_1061_, v_thm_1062_, v_inst_1063_, v_R_1064_, v_a_1065_, v_b_1066_, v_c_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v_thm_1062_);
lean_dec(v___x_1061_);
lean_dec(v_mvarCounterSaved_1059_);
lean_dec(v_upperBound_1058_);
return v_res_1078_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_object* v_00_u03b2_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
uint8_t v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_1080_, v_x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
uint8_t v_res_1086_; lean_object* v_r_1087_; 
v_res_1086_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(v_00_u03b2_1083_, v_x_1084_, v_x_1085_);
lean_dec(v_x_1085_);
lean_dec_ref(v_x_1084_);
v_r_1087_ = lean_box(v_res_1086_);
return v_r_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(lean_object* v_00_u03b2_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_x_1089_, v_x_1090_, v_x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1093_, lean_object* v_x_1094_, size_t v_x_1095_, lean_object* v_x_1096_){
_start:
{
uint8_t v___x_1097_; 
v___x_1097_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_1094_, v_x_1095_, v_x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_x_1101_){
_start:
{
size_t v_x_45196__boxed_1102_; uint8_t v_res_1103_; lean_object* v_r_1104_; 
v_x_45196__boxed_1102_ = lean_unbox_usize(v_x_1100_);
lean_dec(v_x_1100_);
v_res_1103_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(v_00_u03b2_1098_, v_x_1099_, v_x_45196__boxed_1102_, v_x_1101_);
lean_dec(v_x_1101_);
lean_dec_ref(v_x_1099_);
v_r_1104_ = lean_box(v_res_1103_);
return v_r_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(lean_object* v_00_u03b2_1105_, lean_object* v_x_1106_, size_t v_x_1107_, size_t v_x_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_1106_, v_x_1107_, v_x_1108_, v_x_1109_, v_x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
size_t v_x_45207__boxed_1118_; size_t v_x_45208__boxed_1119_; lean_object* v_res_1120_; 
v_x_45207__boxed_1118_ = lean_unbox_usize(v_x_1114_);
lean_dec(v_x_1114_);
v_x_45208__boxed_1119_ = lean_unbox_usize(v_x_1115_);
lean_dec(v_x_1115_);
v_res_1120_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(v_00_u03b2_1112_, v_x_1113_, v_x_45207__boxed_1118_, v_x_45208__boxed_1119_, v_x_1116_, v_x_1117_);
return v_res_1120_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1121_, lean_object* v_keys_1122_, lean_object* v_vals_1123_, lean_object* v_heq_1124_, lean_object* v_i_1125_, lean_object* v_k_1126_){
_start:
{
uint8_t v___x_1127_; 
v___x_1127_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_keys_1122_, v_i_1125_, v_k_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1128_, lean_object* v_keys_1129_, lean_object* v_vals_1130_, lean_object* v_heq_1131_, lean_object* v_i_1132_, lean_object* v_k_1133_){
_start:
{
uint8_t v_res_1134_; lean_object* v_r_1135_; 
v_res_1134_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(v_00_u03b2_1128_, v_keys_1129_, v_vals_1130_, v_heq_1131_, v_i_1132_, v_k_1133_);
lean_dec(v_k_1133_);
lean_dec_ref(v_vals_1130_);
lean_dec_ref(v_keys_1129_);
v_r_1135_ = lean_box(v_res_1134_);
return v_r_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_1136_, lean_object* v_n_1137_, lean_object* v_k_1138_, lean_object* v_v_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11___redArg(v_n_1137_, v_k_1138_, v_v_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1141_, size_t v_depth_1142_, lean_object* v_keys_1143_, lean_object* v_vals_1144_, lean_object* v_heq_1145_, lean_object* v_i_1146_, lean_object* v_entries_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_depth_1142_, v_keys_1143_, v_vals_1144_, v_i_1146_, v_entries_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1149_, lean_object* v_depth_1150_, lean_object* v_keys_1151_, lean_object* v_vals_1152_, lean_object* v_heq_1153_, lean_object* v_i_1154_, lean_object* v_entries_1155_){
_start:
{
size_t v_depth_boxed_1156_; lean_object* v_res_1157_; 
v_depth_boxed_1156_ = lean_unbox_usize(v_depth_1150_);
lean_dec(v_depth_1150_);
v_res_1157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(v_00_u03b2_1149_, v_depth_boxed_1156_, v_keys_1151_, v_vals_1152_, v_heq_1153_, v_i_1154_, v_entries_1155_);
lean_dec_ref(v_vals_1152_);
lean_dec_ref(v_keys_1151_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12___redArg(v_x_1159_, v_x_1160_, v_x_1161_, v_x_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(lean_object* v_fst_1164_, lean_object* v_d_1165_, lean_object* v_x_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1164_, v_x_1166_, v_d_1165_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed(lean_object* v_fst_1178_, lean_object* v_d_1179_, lean_object* v_x_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(v_fst_1178_, v_d_1179_, v_x_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object* v_d_1192_, lean_object* v_e_1193_, lean_object* v_as_1194_, size_t v_sz_1195_, size_t v_i_1196_, lean_object* v_b_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v___y_1209_; lean_object* v___y_1210_; uint8_t v___y_1216_; lean_object* v___y_1217_; uint8_t v___y_1220_; uint8_t v___y_1221_; lean_object* v___y_1222_; uint8_t v___y_1223_; uint8_t v___y_1225_; lean_object* v___y_1226_; uint8_t v___y_1227_; lean_object* v___y_1231_; uint8_t v___y_1232_; uint8_t v___x_1234_; 
v___x_1234_ = lean_usize_dec_lt(v_i_1196_, v_sz_1195_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_d_1192_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_b_1197_);
return v___x_1235_;
}
else
{
lean_object* v_a_1236_; lean_object* v_fst_1237_; lean_object* v_snd_1238_; lean_object* v_snd_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1288_; 
v_a_1236_ = lean_array_uget_borrowed(v_as_1194_, v_i_1196_);
v_fst_1237_ = lean_ctor_get(v_a_1236_, 0);
v_snd_1238_ = lean_ctor_get(v_a_1236_, 1);
v_snd_1239_ = lean_ctor_get(v_b_1197_, 1);
v_isSharedCheck_1288_ = !lean_is_exclusive(v_b_1197_);
if (v_isSharedCheck_1288_ == 0)
{
lean_object* v_unused_1289_; 
v_unused_1289_ = lean_ctor_get(v_b_1197_, 0);
lean_dec(v_unused_1289_);
v___x_1241_ = v_b_1197_;
v_isShared_1242_ = v_isSharedCheck_1288_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_snd_1239_);
lean_dec(v_b_1197_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1288_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___y_1245_; uint8_t v_done_1246_; uint8_t v___y_1247_; lean_object* v_result_1257_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1243_ = lean_box(0);
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = lean_nat_dec_eq(v_snd_1238_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___f_1267_; lean_object* v___x_1268_; 
lean_inc_ref(v_d_1192_);
lean_inc(v_fst_1237_);
v___f_1267_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1267_, 0, v_fst_1237_);
lean_closure_set(v___f_1267_, 1, v_d_1192_);
lean_inc_ref(v_e_1193_);
v___x_1268_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_1193_, v_snd_1238_, v___f_1267_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___x_1268_, 1);
v_result_1257_ = v_a_1269_;
goto v___jp_1256_;
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_del_object(v___x_1241_);
lean_dec(v_snd_1239_);
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_d_1192_);
v_a_1270_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1268_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1268_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v___x_1278_; 
lean_inc_ref(v_d_1192_);
lean_inc_ref(v_e_1193_);
lean_inc(v_fst_1237_);
v___x_1278_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1237_, v_e_1193_, v_d_1192_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v_result_1257_ = v_a_1279_;
goto v___jp_1256_;
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
lean_del_object(v___x_1241_);
lean_dec(v_snd_1239_);
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_d_1192_);
v_a_1280_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1278_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1278_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
v___jp_1244_:
{
if (v_done_1246_ == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
lean_dec_ref(v___y_1245_);
v___x_1248_ = lean_box(v___y_1247_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v___x_1248_);
lean_ctor_set(v___x_1241_, 0, v___x_1243_);
v___x_1250_ = v___x_1241_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
size_t v___x_1251_; size_t v___x_1252_; 
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = lean_usize_add(v_i_1196_, v___x_1251_);
v_i_1196_ = v___x_1252_;
v_b_1197_ = v___x_1250_;
goto _start;
}
}
else
{
uint8_t v___x_1255_; 
lean_del_object(v___x_1241_);
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_d_1192_);
v___x_1255_ = 0;
v___y_1225_ = v___y_1247_;
v___y_1226_ = v___y_1245_;
v___y_1227_ = v___x_1255_;
goto v___jp_1224_;
}
}
v___jp_1256_:
{
uint8_t v___x_1258_; 
v___x_1258_ = lean_unbox(v_snd_1239_);
if (v___x_1258_ == 0)
{
lean_dec(v_snd_1239_);
if (lean_obj_tag(v_result_1257_) == 0)
{
uint8_t v_done_1259_; uint8_t v_contextDependent_1260_; 
v_done_1259_ = lean_ctor_get_uint8(v_result_1257_, 0);
v_contextDependent_1260_ = lean_ctor_get_uint8(v_result_1257_, 1);
v___y_1245_ = v_result_1257_;
v_done_1246_ = v_done_1259_;
v___y_1247_ = v_contextDependent_1260_;
goto v___jp_1244_;
}
else
{
uint8_t v_contextDependent_1261_; 
lean_del_object(v___x_1241_);
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_d_1192_);
v_contextDependent_1261_ = lean_ctor_get_uint8(v_result_1257_, sizeof(void*)*2 + 1);
v___y_1231_ = v_result_1257_;
v___y_1232_ = v_contextDependent_1261_;
goto v___jp_1230_;
}
}
else
{
if (lean_obj_tag(v_result_1257_) == 0)
{
uint8_t v_done_1262_; uint8_t v___x_1263_; 
v_done_1262_ = lean_ctor_get_uint8(v_result_1257_, 0);
v___x_1263_ = lean_unbox(v_snd_1239_);
lean_dec(v_snd_1239_);
v___y_1245_ = v_result_1257_;
v_done_1246_ = v_done_1262_;
v___y_1247_ = v___x_1263_;
goto v___jp_1244_;
}
else
{
uint8_t v___x_1264_; 
lean_del_object(v___x_1241_);
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_d_1192_);
v___x_1264_ = lean_unbox(v_snd_1239_);
lean_dec(v_snd_1239_);
v___y_1231_ = v_result_1257_;
v___y_1232_ = v___x_1264_;
goto v___jp_1230_;
}
}
}
}
}
v___jp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___y_1210_);
v___x_1212_ = lean_box(v___y_1209_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1211_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
return v___x_1214_;
}
v___jp_1215_:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1217_);
v___y_1209_ = v___y_1216_;
v___y_1210_ = v___x_1218_;
goto v___jp_1208_;
}
v___jp_1219_:
{
if (v___y_1223_ == 0)
{
v___y_1216_ = v___y_1220_;
v___y_1217_ = v___y_1222_;
goto v___jp_1215_;
}
else
{
if (v___y_1221_ == 0)
{
v___y_1209_ = v___y_1220_;
v___y_1210_ = v___y_1222_;
goto v___jp_1208_;
}
else
{
v___y_1216_ = v___y_1220_;
v___y_1217_ = v___y_1222_;
goto v___jp_1215_;
}
}
}
v___jp_1224_:
{
if (v___y_1225_ == 0)
{
v___y_1209_ = v___y_1225_;
v___y_1210_ = v___y_1226_;
goto v___jp_1208_;
}
else
{
if (lean_obj_tag(v___y_1226_) == 0)
{
uint8_t v_contextDependent_1228_; 
v_contextDependent_1228_ = lean_ctor_get_uint8(v___y_1226_, 1);
v___y_1220_ = v___y_1225_;
v___y_1221_ = v___y_1227_;
v___y_1222_ = v___y_1226_;
v___y_1223_ = v_contextDependent_1228_;
goto v___jp_1219_;
}
else
{
uint8_t v_contextDependent_1229_; 
v_contextDependent_1229_ = lean_ctor_get_uint8(v___y_1226_, sizeof(void*)*2 + 1);
v___y_1220_ = v___y_1225_;
v___y_1221_ = v___y_1227_;
v___y_1222_ = v___y_1226_;
v___y_1223_ = v_contextDependent_1229_;
goto v___jp_1219_;
}
}
}
v___jp_1230_:
{
uint8_t v___x_1233_; 
v___x_1233_ = 0;
v___y_1225_ = v___y_1232_;
v___y_1226_ = v___y_1231_;
v___y_1227_ = v___x_1233_;
goto v___jp_1224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object* v_d_1290_, lean_object* v_e_1291_, lean_object* v_as_1292_, lean_object* v_sz_1293_, lean_object* v_i_1294_, lean_object* v_b_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
size_t v_sz_boxed_1306_; size_t v_i_boxed_1307_; lean_object* v_res_1308_; 
v_sz_boxed_1306_ = lean_unbox_usize(v_sz_1293_);
lean_dec(v_sz_1293_);
v_i_boxed_1307_ = lean_unbox_usize(v_i_1294_);
lean_dec(v_i_1294_);
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1290_, v_e_1291_, v_as_1292_, v_sz_boxed_1306_, v_i_boxed_1307_, v_b_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v_as_1292_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object* v_thms_1313_, lean_object* v_d_1314_, lean_object* v_e_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1326_; lean_object* v_mctx_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; size_t v_sz_1330_; size_t v___x_1331_; lean_object* v___x_1332_; 
v___x_1326_ = lean_st_ref_get(v_a_1322_);
v_mctx_1327_ = lean_ctor_get(v___x_1326_, 0);
lean_inc_ref(v_mctx_1327_);
lean_dec(v___x_1326_);
v___x_1328_ = l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(v_thms_1313_, v_mctx_1327_, v_e_1315_);
lean_dec_ref(v_mctx_1327_);
v___x_1329_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0));
v_sz_1330_ = lean_array_size(v___x_1328_);
v___x_1331_ = ((size_t)0ULL);
v___x_1332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1314_, v_e_1315_, v___x_1328_, v_sz_1330_, v___x_1331_, v___x_1329_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec_ref(v___x_1328_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1348_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1335_ = v___x_1332_;
v_isShared_1336_ = v_isSharedCheck_1348_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1332_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1348_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v_fst_1337_; 
v_fst_1337_ = lean_ctor_get(v_a_1333_, 0);
if (lean_obj_tag(v_fst_1337_) == 0)
{
lean_object* v_snd_1338_; uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1342_; 
v_snd_1338_ = lean_ctor_get(v_a_1333_, 1);
lean_inc(v_snd_1338_);
lean_dec(v_a_1333_);
v___x_1339_ = lean_unbox(v_snd_1338_);
lean_dec(v_snd_1338_);
v___x_1340_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1339_);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v___x_1340_);
v___x_1342_ = v___x_1335_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
else
{
lean_object* v_val_1344_; lean_object* v___x_1346_; 
lean_inc_ref(v_fst_1337_);
lean_dec(v_a_1333_);
v_val_1344_ = lean_ctor_get(v_fst_1337_, 0);
lean_inc(v_val_1344_);
lean_dec_ref_known(v_fst_1337_, 1);
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_val_1344_);
v___x_1346_ = v___x_1335_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_val_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
v_a_1349_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1332_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1332_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object* v_thms_1357_, lean_object* v_d_1358_, lean_object* v_e_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_thms_1357_, v_d_1358_, v_e_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_thms_1357_);
return v_res_1370_;
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
