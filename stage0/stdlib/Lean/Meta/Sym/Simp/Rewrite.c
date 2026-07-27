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
v___x_112_ = lean_st_ref_set(v___y_93_, v___x_111_);
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
size_t v_x_48008__boxed_271_; uint8_t v_res_272_; lean_object* v_r_273_; 
v_x_48008__boxed_271_ = lean_unbox_usize(v_x_269_);
lean_dec(v_x_269_);
v_res_272_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_268_, v_x_48008__boxed_271_, v_x_270_);
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
size_t v_x_48151__boxed_437_; size_t v_x_48152__boxed_438_; lean_object* v_res_439_; 
v_x_48151__boxed_437_ = lean_unbox_usize(v_x_433_);
lean_dec(v_x_433_);
v_x_48152__boxed_438_ = lean_unbox_usize(v_x_434_);
lean_dec(v_x_434_);
v_res_439_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_432_, v_x_48151__boxed_437_, v_x_48152__boxed_438_, v_x_435_, v_x_436_);
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
lean_object* v___x_451_; lean_object* v_mctx_452_; lean_object* v_cache_453_; lean_object* v_zetaDeltaFVarIds_454_; lean_object* v_postponed_455_; lean_object* v_diag_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_484_; 
v___x_451_ = lean_st_ref_take(v___y_449_);
v_mctx_452_ = lean_ctor_get(v___x_451_, 0);
v_cache_453_ = lean_ctor_get(v___x_451_, 1);
v_zetaDeltaFVarIds_454_ = lean_ctor_get(v___x_451_, 2);
v_postponed_455_ = lean_ctor_get(v___x_451_, 3);
v_diag_456_ = lean_ctor_get(v___x_451_, 4);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_484_ == 0)
{
v___x_458_ = v___x_451_;
v_isShared_459_ = v_isSharedCheck_484_;
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
v_isShared_459_ = v_isSharedCheck_484_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v_depth_460_; lean_object* v_levelAssignDepth_461_; lean_object* v_lmvarCounter_462_; lean_object* v_mvarCounter_463_; lean_object* v_lDecls_464_; lean_object* v_decls_465_; lean_object* v_userNames_466_; lean_object* v_lAssignment_467_; lean_object* v_eAssignment_468_; lean_object* v_dAssignment_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_483_; 
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
v_isSharedCheck_483_ = !lean_is_exclusive(v_mctx_452_);
if (v_isSharedCheck_483_ == 0)
{
v___x_471_ = v_mctx_452_;
v_isShared_472_ = v_isSharedCheck_483_;
goto v_resetjp_470_;
}
else
{
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
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_483_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_473_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_eAssignment_468_, v_mvarId_447_, v_val_448_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 8, v___x_473_);
v___x_475_ = v___x_471_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_depth_460_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_levelAssignDepth_461_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_lmvarCounter_462_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_mvarCounter_463_);
lean_ctor_set(v_reuseFailAlloc_482_, 4, v_lDecls_464_);
lean_ctor_set(v_reuseFailAlloc_482_, 5, v_decls_465_);
lean_ctor_set(v_reuseFailAlloc_482_, 6, v_userNames_466_);
lean_ctor_set(v_reuseFailAlloc_482_, 7, v_lAssignment_467_);
lean_ctor_set(v_reuseFailAlloc_482_, 8, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_482_, 9, v_dAssignment_469_);
v___x_475_ = v_reuseFailAlloc_482_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 0, v___x_475_);
v___x_477_ = v___x_458_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_cache_453_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_zetaDeltaFVarIds_454_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_postponed_455_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_diag_456_);
v___x_477_ = v_reuseFailAlloc_481_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_st_ref_set(v___y_449_, v___x_477_);
v___x_479_ = lean_box(0);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg___boxed(lean_object* v_mvarId_485_, lean_object* v_val_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_485_, v_val_486_, v___y_487_);
lean_dec(v___y_487_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(lean_object* v_mvarId_490_, lean_object* v_fst_491_, lean_object* v_a_492_, uint8_t v___y_493_, lean_object* v___x_494_, lean_object* v_val_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
lean_inc_ref(v_val_495_);
v___x_506_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_490_, v_val_495_, v___y_502_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_518_; 
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v___x_506_, 0);
lean_dec(v_unused_519_);
v___x_508_ = v___x_506_;
v_isShared_509_ = v_isSharedCheck_518_;
goto v_resetjp_507_;
}
else
{
lean_dec(v___x_506_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_518_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_510_ = lean_array_fset(v_fst_491_, v_a_492_, v_val_495_);
v___x_511_ = lean_box(v___y_493_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_494_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_514_);
v___x_516_ = v___x_508_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec_ref(v_val_495_);
lean_dec(v___x_494_);
lean_dec(v_fst_491_);
v_a_520_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_506_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_506_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0___boxed(lean_object* v_mvarId_528_, lean_object* v_fst_529_, lean_object* v_a_530_, lean_object* v___y_531_, lean_object* v___x_532_, lean_object* v_val_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
uint8_t v___y_48365__boxed_544_; lean_object* v_res_545_; 
v___y_48365__boxed_544_ = lean_unbox(v___y_531_);
v_res_545_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_528_, v_fst_529_, v_a_530_, v___y_48365__boxed_544_, v___x_532_, v_val_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec(v_a_530_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(lean_object* v_upperBound_546_, lean_object* v_mvarCounterSaved_547_, lean_object* v_d_548_, lean_object* v_thm_549_, lean_object* v_a_550_, lean_object* v_b_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_a_563_; lean_object* v___y_568_; uint8_t v___x_587_; 
v___x_587_ = lean_nat_dec_lt(v_a_550_, v_upperBound_546_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v_b_551_);
return v___x_588_;
}
else
{
lean_object* v_snd_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_742_; 
v_snd_589_ = lean_ctor_get(v_b_551_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_b_551_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v_b_551_, 0);
lean_dec(v_unused_743_);
v___x_591_ = v_b_551_;
v_isShared_592_ = v_isSharedCheck_742_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_snd_589_);
lean_dec(v_b_551_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_742_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v_fst_593_; lean_object* v_snd_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_741_; 
v_fst_593_ = lean_ctor_get(v_snd_589_, 0);
v_snd_594_ = lean_ctor_get(v_snd_589_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_snd_589_);
if (v_isSharedCheck_741_ == 0)
{
v___x_596_ = v_snd_589_;
v_isShared_597_ = v_isSharedCheck_741_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_snd_594_);
lean_inc(v_fst_593_);
lean_dec(v_snd_589_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_741_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_box(0);
v___x_599_ = lean_array_fget_borrowed(v_fst_593_, v_a_550_);
if (lean_obj_tag(v___x_599_) == 2)
{
lean_object* v_mvarId_600_; lean_object* v___x_601_; 
v_mvarId_600_ = lean_ctor_get(v___x_599_, 0);
v___x_601_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_600_, v___y_558_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; uint8_t v___x_603_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v___x_603_ = lean_unbox(v_a_602_);
lean_dec(v_a_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
lean_inc(v_mvarId_600_);
v___x_604_ = l_Lean_MVarId_getDecl(v_mvarId_600_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v_type_606_; lean_object* v_index_607_; uint8_t v___x_608_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
v_type_606_ = lean_ctor_get(v_a_605_, 2);
lean_inc_ref(v_type_606_);
v_index_607_ = lean_ctor_get(v_a_605_, 6);
lean_inc(v_index_607_);
lean_dec(v_a_605_);
v___x_608_ = lean_nat_dec_le(v_mvarCounterSaved_547_, v_index_607_);
lean_dec(v_index_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_610_; 
lean_dec_ref(v_type_606_);
if (v_isShared_597_ == 0)
{
v___x_610_ = v___x_596_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_fst_593_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_snd_594_);
v___x_610_ = v_reuseFailAlloc_614_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_612_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_610_);
lean_ctor_set(v___x_591_, 0, v___x_598_);
v___x_612_ = v___x_591_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
v_a_563_ = v___x_612_;
goto v___jp_562_;
}
}
}
else
{
lean_object* v___x_615_; 
lean_inc_ref(v_d_548_);
lean_inc(v___y_560_);
lean_inc_ref(v___y_559_);
lean_inc(v___y_558_);
lean_inc_ref(v___y_557_);
lean_inc(v___y_556_);
lean_inc_ref(v___y_555_);
lean_inc(v___y_554_);
lean_inc_ref(v___y_553_);
lean_inc(v___y_552_);
v___x_615_ = lean_apply_11(v_d_548_, v_type_606_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, lean_box(0));
if (lean_obj_tag(v___x_615_) == 0)
{
lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_675_; 
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_675_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_675_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_675_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
uint8_t v___y_621_; 
if (lean_obj_tag(v_a_616_) == 0)
{
uint8_t v___x_634_; 
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v___x_634_ = lean_unbox(v_snd_594_);
lean_dec(v_snd_594_);
if (v___x_634_ == 0)
{
uint8_t v_contextDependent_635_; 
v_contextDependent_635_ = lean_ctor_get_uint8(v_a_616_, 0);
lean_dec_ref_known(v_a_616_, 0);
v___y_621_ = v_contextDependent_635_;
goto v___jp_620_;
}
else
{
lean_dec_ref_known(v_a_616_, 0);
v___y_621_ = v___x_608_;
goto v___jp_620_;
}
}
else
{
lean_object* v_proof_636_; uint8_t v_contextDependent_637_; uint8_t v___y_639_; uint8_t v___x_674_; 
lean_inc(v_mvarId_600_);
lean_del_object(v___x_618_);
lean_del_object(v___x_596_);
lean_del_object(v___x_591_);
v_proof_636_ = lean_ctor_get(v_a_616_, 0);
lean_inc_ref(v_proof_636_);
v_contextDependent_637_ = lean_ctor_get_uint8(v_a_616_, sizeof(void*)*1);
lean_dec_ref_known(v_a_616_, 1);
v___x_674_ = lean_unbox(v_snd_594_);
lean_dec(v_snd_594_);
if (v___x_674_ == 0)
{
v___y_639_ = v_contextDependent_637_;
goto v___jp_638_;
}
else
{
v___y_639_ = v___x_608_;
goto v___jp_638_;
}
v___jp_638_:
{
lean_object* v_rhsVarMask_640_; uint8_t v___x_641_; 
v_rhsVarMask_640_ = lean_ctor_get(v_thm_549_, 3);
v___x_641_ = l_Nat_testBit(v_rhsVarMask_640_, v_a_550_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_proof_636_, v___y_558_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_600_, v_fst_593_, v_a_550_, v___y_639_, v___x_598_, v_a_643_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
v___y_568_ = v___x_644_;
goto v___jp_567_;
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_mvarId_600_);
lean_dec(v_fst_593_);
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v_a_645_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_642_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_642_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
else
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_instantiateMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__4___redArg(v_proof_636_, v___y_558_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v___x_655_ = l_Lean_Meta_Sym_shareCommon(v_a_654_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___lam__0(v_mvarId_600_, v_fst_593_, v_a_550_, v___y_639_, v___x_598_, v_a_656_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
v___y_568_ = v___x_657_;
goto v___jp_567_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec(v_mvarId_600_);
lean_dec(v_fst_593_);
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v_a_658_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_655_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_655_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec(v_mvarId_600_);
lean_dec(v_fst_593_);
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v_a_666_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_653_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_653_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
v___jp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_622_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___y_621_);
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
v___x_624_ = lean_box(v___y_621_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 1, v___x_624_);
v___x_626_ = v___x_596_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_fst_593_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_624_);
v___x_626_ = v_reuseFailAlloc_633_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
lean_object* v___x_628_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_626_);
lean_ctor_set(v___x_591_, 0, v___x_623_);
v___x_628_ = v___x_591_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_626_);
v___x_628_ = v_reuseFailAlloc_632_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_630_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 0, v___x_628_);
v___x_630_ = v___x_618_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_del_object(v___x_596_);
lean_dec(v_snd_594_);
lean_dec(v_fst_593_);
lean_del_object(v___x_591_);
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v_a_676_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_615_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_615_);
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
}
else
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_691_; 
lean_del_object(v___x_596_);
lean_dec(v_snd_594_);
lean_dec(v_fst_593_);
lean_del_object(v___x_591_);
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v_a_684_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_691_ == 0)
{
v___x_686_ = v___x_604_;
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_604_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_691_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_689_; 
if (v_isShared_687_ == 0)
{
v___x_689_ = v___x_686_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_a_684_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
}
else
{
lean_object* v___x_692_; 
lean_inc_ref(v___x_599_);
v___x_692_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_599_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v___x_694_ = lean_array_fset(v_fst_593_, v_a_550_, v_a_693_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_694_);
v___x_696_ = v___x_596_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_snd_594_);
v___x_696_ = v_reuseFailAlloc_700_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_696_);
lean_ctor_set(v___x_591_, 0, v___x_598_);
v___x_698_ = v___x_591_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
v_a_563_ = v___x_698_;
goto v___jp_562_;
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_del_object(v___x_596_);
lean_dec(v_snd_594_);
lean_dec(v_fst_593_);
lean_del_object(v___x_591_);
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v_a_701_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_692_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_692_);
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
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_del_object(v___x_596_);
lean_dec(v_snd_594_);
lean_dec(v_fst_593_);
lean_del_object(v___x_591_);
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v_a_709_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_601_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_601_);
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
uint8_t v___x_717_; 
v___x_717_ = l_Lean_Expr_hasMVar(v___x_599_);
if (v___x_717_ == 0)
{
lean_object* v___x_719_; 
if (v_isShared_597_ == 0)
{
v___x_719_ = v___x_596_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_fst_593_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_snd_594_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_719_);
lean_ctor_set(v___x_591_, 0, v___x_598_);
v___x_721_ = v___x_591_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v_a_563_ = v___x_721_;
goto v___jp_562_;
}
}
}
else
{
lean_object* v___x_724_; 
lean_inc(v___x_599_);
v___x_724_ = l_Lean_Meta_Sym_instantiateMVarsS(v___x_599_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
v___x_726_ = lean_array_fset(v_fst_593_, v_a_550_, v_a_725_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_726_);
v___x_728_ = v___x_596_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_snd_594_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_730_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v___x_728_);
lean_ctor_set(v___x_591_, 0, v___x_598_);
v___x_730_ = v___x_591_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_598_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
v_a_563_ = v___x_730_;
goto v___jp_562_;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_del_object(v___x_596_);
lean_dec(v_snd_594_);
lean_dec(v_fst_593_);
lean_del_object(v___x_591_);
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v_a_733_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_724_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_724_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
}
}
}
v___jp_562_:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = lean_nat_add(v_a_550_, v___x_564_);
lean_dec(v_a_550_);
v_a_550_ = v___x_565_;
v_b_551_ = v_a_563_;
goto _start;
}
v___jp_567_:
{
if (lean_obj_tag(v___y_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_578_; 
v_a_569_ = lean_ctor_get(v___y_568_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___y_568_);
if (v_isSharedCheck_578_ == 0)
{
v___x_571_ = v___y_568_;
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___y_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_578_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
if (lean_obj_tag(v_a_569_) == 0)
{
lean_object* v_a_573_; lean_object* v___x_575_; 
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v_a_573_ = lean_ctor_get(v_a_569_, 0);
lean_inc(v_a_573_);
lean_dec_ref_known(v_a_569_, 1);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_a_573_);
v___x_575_ = v___x_571_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
lean_object* v_a_577_; 
lean_del_object(v___x_571_);
v_a_577_ = lean_ctor_get(v_a_569_, 0);
lean_inc(v_a_577_);
lean_dec_ref_known(v_a_569_, 1);
v_a_563_ = v_a_577_;
goto v___jp_562_;
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec(v_a_550_);
lean_dec_ref(v_d_548_);
v_a_579_ = lean_ctor_get(v___y_568_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___y_568_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___y_568_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___y_568_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg___boxed(lean_object* v_upperBound_744_, lean_object* v_mvarCounterSaved_745_, lean_object* v_d_746_, lean_object* v_thm_747_, lean_object* v_a_748_, lean_object* v_b_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_upperBound_744_, v_mvarCounterSaved_745_, v_d_746_, v_thm_747_, v_a_748_, v_b_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v_thm_747_);
lean_dec(v_mvarCounterSaved_745_);
lean_dec(v_upperBound_744_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = l_List_reverse___redArg(v_x_762_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
else
{
lean_object* v_head_775_; lean_object* v_tail_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_786_; 
v_head_775_ = lean_ctor_get(v_x_761_, 0);
v_tail_776_ = lean_ctor_get(v_x_761_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_786_ == 0)
{
v___x_778_ = v_x_761_;
v_isShared_779_ = v_isSharedCheck_786_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_tail_776_);
lean_inc(v_head_775_);
lean_dec(v_x_761_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_786_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_780_; lean_object* v_a_781_; lean_object* v___x_783_; 
v___x_780_ = l_Lean_instantiateLevelMVars___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__0___redArg(v_head_775_, v___y_769_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref(v___x_780_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 1, v_x_762_);
lean_ctor_set(v___x_778_, 0, v_a_781_);
v___x_783_ = v___x_778_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_781_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_x_762_);
v___x_783_ = v_reuseFailAlloc_785_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
v_x_761_ = v_tail_776_;
v_x_762_ = v___x_783_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1___boxed(lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_x_787_, v_x_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec(v___y_791_);
lean_dec_ref(v___y_790_);
lean_dec(v___y_789_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(lean_object* v_thm_802_, lean_object* v_e_803_, lean_object* v_d_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; lean_object* v_mctx_816_; lean_object* v_expr_817_; lean_object* v_pattern_818_; lean_object* v_rhs_819_; uint8_t v_perm_820_; uint8_t v___x_821_; lean_object* v___x_822_; 
v___x_815_ = lean_st_ref_get(v___y_811_);
v_mctx_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc_ref(v_mctx_816_);
lean_dec(v___x_815_);
v_expr_817_ = lean_ctor_get(v_thm_802_, 0);
lean_inc_ref(v_expr_817_);
v_pattern_818_ = lean_ctor_get(v_thm_802_, 1);
lean_inc_ref_n(v_pattern_818_, 2);
v_rhs_819_ = lean_ctor_get(v_thm_802_, 2);
lean_inc_ref(v_rhs_819_);
v_perm_820_ = lean_ctor_get_uint8(v_thm_802_, sizeof(void*)*4);
v___x_821_ = 1;
lean_inc_ref(v_e_803_);
v___x_822_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pattern_818_, v_e_803_, v___x_821_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_936_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_936_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_936_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_936_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
if (lean_obj_tag(v_a_823_) == 1)
{
lean_object* v_val_827_; lean_object* v_us_828_; lean_object* v_args_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
lean_del_object(v___x_825_);
v_val_827_ = lean_ctor_get(v_a_823_, 0);
lean_inc(v_val_827_);
lean_dec_ref_known(v_a_823_, 1);
v_us_828_ = lean_ctor_get(v_val_827_, 0);
lean_inc(v_us_828_);
v_args_829_ = lean_ctor_get(v_val_827_, 1);
lean_inc_ref(v_args_829_);
lean_dec(v_val_827_);
v___x_830_ = lean_box(0);
v___x_831_ = l_List_mapM_loop___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__1(v_us_828_, v___x_830_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v_mvarCounter_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
v_mvarCounter_833_ = lean_ctor_get(v_mctx_816_, 3);
lean_inc(v_mvarCounter_833_);
lean_dec_ref(v_mctx_816_);
v___x_834_ = lean_array_get_size(v_args_829_);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = 0;
v___x_837_ = lean_box(0);
v___x_838_ = lean_box(v___x_836_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v_args_829_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
v___x_840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_837_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v___x_834_, v_mvarCounter_833_, v_d_804_, v_thm_802_, v___x_835_, v___x_840_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
lean_dec_ref(v_thm_802_);
lean_dec(v_mvarCounter_833_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_915_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_915_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_915_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_915_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_fst_846_; 
v_fst_846_ = lean_ctor_get(v_a_842_, 0);
if (lean_obj_tag(v_fst_846_) == 0)
{
lean_object* v_snd_847_; lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v_levelParams_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_del_object(v___x_844_);
v_snd_847_ = lean_ctor_get(v_a_842_, 1);
lean_inc(v_snd_847_);
lean_dec(v_a_842_);
v_fst_848_ = lean_ctor_get(v_snd_847_, 0);
lean_inc(v_fst_848_);
v_snd_849_ = lean_ctor_get(v_snd_847_, 1);
lean_inc(v_snd_849_);
lean_dec(v_snd_847_);
v_levelParams_850_ = lean_ctor_get(v_pattern_818_, 0);
lean_inc(v_levelParams_850_);
lean_inc(v_a_832_);
v___x_851_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_mkValue(v_expr_817_, v_pattern_818_, v_a_832_, v_fst_848_);
v___x_852_ = l_Lean_Expr_instantiateLevelParams(v_rhs_819_, v_levelParams_850_, v_a_832_);
lean_dec_ref(v_rhs_819_);
v___x_853_ = l_Lean_Meta_Sym_shareCommonInc(v___x_852_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_855_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
v___x_855_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_a_854_, v_fst_848_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_894_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_894_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_894_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_894_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
size_t v___x_860_; size_t v___x_861_; uint8_t v___x_862_; 
v___x_860_ = lean_ptr_addr(v_e_803_);
v___x_861_ = lean_ptr_addr(v_a_856_);
v___x_862_ = lean_usize_dec_eq(v___x_860_, v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
lean_inc(v_a_856_);
v___x_863_ = l___private_Lean_Meta_Sym_Simp_Rewrite_0__Lean_Meta_Sym_Simp_Theorem_rewrite_checkPerm(v_perm_820_, v_e_803_, v_a_856_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
if (lean_obj_tag(v___x_863_) == 0)
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_880_; 
v_a_864_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_880_ == 0)
{
v___x_866_ = v___x_863_;
v_isShared_867_ = v_isSharedCheck_880_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_863_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_880_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v___x_874_; 
v___x_874_ = lean_unbox(v_a_864_);
lean_dec(v_a_864_);
if (v___x_874_ == 0)
{
lean_del_object(v___x_858_);
lean_dec(v_a_856_);
lean_dec_ref(v___x_851_);
goto v___jp_868_;
}
else
{
if (v___x_862_ == 0)
{
lean_object* v___x_875_; uint8_t v___x_876_; lean_object* v___x_878_; 
lean_del_object(v___x_866_);
v___x_875_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_875_, 0, v_a_856_);
lean_ctor_set(v___x_875_, 1, v___x_851_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*2, v___x_836_);
v___x_876_ = lean_unbox(v_snd_849_);
lean_dec(v_snd_849_);
lean_ctor_set_uint8(v___x_875_, sizeof(void*)*2 + 1, v___x_876_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_875_);
v___x_878_ = v___x_858_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_875_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
else
{
lean_del_object(v___x_858_);
lean_dec(v_a_856_);
lean_dec_ref(v___x_851_);
goto v___jp_868_;
}
}
v___jp_868_:
{
uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_869_ = lean_unbox(v_snd_849_);
lean_dec(v_snd_849_);
v___x_870_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_869_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 0, v___x_870_);
v___x_872_ = v___x_866_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_del_object(v___x_858_);
lean_dec(v_a_856_);
lean_dec_ref(v___x_851_);
lean_dec(v_snd_849_);
v_a_881_ = lean_ctor_get(v___x_863_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_863_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_863_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_863_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
uint8_t v___x_889_; lean_object* v___x_890_; lean_object* v___x_892_; 
lean_dec(v_a_856_);
lean_dec_ref(v___x_851_);
lean_dec_ref(v_e_803_);
v___x_889_ = lean_unbox(v_snd_849_);
lean_dec(v_snd_849_);
v___x_890_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_889_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_890_);
v___x_892_ = v___x_858_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v___x_851_);
lean_dec(v_snd_849_);
lean_dec_ref(v_e_803_);
v_a_895_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_855_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_855_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v___x_851_);
lean_dec(v_snd_849_);
lean_dec(v_fst_848_);
lean_dec_ref(v_e_803_);
v_a_903_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_853_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_853_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_val_911_; lean_object* v___x_913_; 
lean_inc_ref(v_fst_846_);
lean_dec(v_a_842_);
lean_dec(v_a_832_);
lean_dec_ref(v_rhs_819_);
lean_dec_ref(v_pattern_818_);
lean_dec_ref(v_expr_817_);
lean_dec_ref(v_e_803_);
v_val_911_ = lean_ctor_get(v_fst_846_, 0);
lean_inc(v_val_911_);
lean_dec_ref_known(v_fst_846_, 1);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v_val_911_);
v___x_913_ = v___x_844_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_val_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_a_832_);
lean_dec_ref(v_rhs_819_);
lean_dec_ref(v_pattern_818_);
lean_dec_ref(v_expr_817_);
lean_dec_ref(v_e_803_);
v_a_916_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_841_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_841_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v_args_829_);
lean_dec_ref(v_rhs_819_);
lean_dec_ref(v_pattern_818_);
lean_dec_ref(v_expr_817_);
lean_dec_ref(v_mctx_816_);
lean_dec_ref(v_d_804_);
lean_dec_ref(v_e_803_);
lean_dec_ref(v_thm_802_);
v_a_924_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_831_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_831_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v___x_932_; lean_object* v___x_934_; 
lean_dec(v_a_823_);
lean_dec_ref(v_rhs_819_);
lean_dec_ref(v_pattern_818_);
lean_dec_ref(v_expr_817_);
lean_dec_ref(v_mctx_816_);
lean_dec_ref(v_d_804_);
lean_dec_ref(v_e_803_);
lean_dec_ref(v_thm_802_);
v___x_932_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___closed__0));
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_932_);
v___x_934_ = v___x_825_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v_rhs_819_);
lean_dec_ref(v_pattern_818_);
lean_dec_ref(v_expr_817_);
lean_dec_ref(v_mctx_816_);
lean_dec_ref(v_d_804_);
lean_dec_ref(v_e_803_);
lean_dec_ref(v_thm_802_);
v_a_937_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_822_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_822_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed(lean_object* v_thm_945_, lean_object* v_e_946_, lean_object* v_d_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0(v_thm_945_, v_e_946_, v_d_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object* v_thm_959_, lean_object* v_e_960_, lean_object* v_d_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___f_972_; uint8_t v___x_973_; lean_object* v___x_974_; 
v___f_972_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_Theorem_rewrite___lam__0___boxed), 13, 3);
lean_closure_set(v___f_972_, 0, v_thm_959_);
lean_closure_set(v___f_972_, 1, v_e_960_);
lean_closure_set(v___f_972_, 2, v_d_961_);
v___x_973_ = 0;
v___x_974_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__6___redArg(v___f_972_, v___x_973_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite___boxed(lean_object* v_thm_975_, lean_object* v_e_976_, lean_object* v_d_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_thm_975_, v_e_976_, v_d_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(lean_object* v_mvarId_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___redArg(v_mvarId_989_, v___y_996_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2___boxed(lean_object* v_mvarId_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2(v_mvarId_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec(v_mvarId_1001_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(lean_object* v_mvarId_1013_, lean_object* v_val_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___redArg(v_mvarId_1013_, v_val_1014_, v___y_1021_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3___boxed(lean_object* v_mvarId_1026_, lean_object* v_val_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3(v_mvarId_1026_, v_val_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(lean_object* v_upperBound_1039_, lean_object* v_mvarCounterSaved_1040_, lean_object* v_d_1041_, lean_object* v___x_1042_, lean_object* v_thm_1043_, lean_object* v_inst_1044_, lean_object* v_R_1045_, lean_object* v_a_1046_, lean_object* v_b_1047_, lean_object* v_c_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___redArg(v_upperBound_1039_, v_mvarCounterSaved_1040_, v_d_1041_, v_thm_1043_, v_a_1046_, v_b_1047_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_1060_ = _args[0];
lean_object* v_mvarCounterSaved_1061_ = _args[1];
lean_object* v_d_1062_ = _args[2];
lean_object* v___x_1063_ = _args[3];
lean_object* v_thm_1064_ = _args[4];
lean_object* v_inst_1065_ = _args[5];
lean_object* v_R_1066_ = _args[6];
lean_object* v_a_1067_ = _args[7];
lean_object* v_b_1068_ = _args[8];
lean_object* v_c_1069_ = _args[9];
lean_object* v___y_1070_ = _args[10];
lean_object* v___y_1071_ = _args[11];
lean_object* v___y_1072_ = _args[12];
lean_object* v___y_1073_ = _args[13];
lean_object* v___y_1074_ = _args[14];
lean_object* v___y_1075_ = _args[15];
lean_object* v___y_1076_ = _args[16];
lean_object* v___y_1077_ = _args[17];
lean_object* v___y_1078_ = _args[18];
lean_object* v___y_1079_ = _args[19];
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__5(v_upperBound_1060_, v_mvarCounterSaved_1061_, v_d_1062_, v___x_1063_, v_thm_1064_, v_inst_1065_, v_R_1066_, v_a_1067_, v_b_1068_, v_c_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v_thm_1064_);
lean_dec(v___x_1063_);
lean_dec(v_mvarCounterSaved_1061_);
lean_dec(v_upperBound_1060_);
return v_res_1080_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(lean_object* v_00_u03b2_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
uint8_t v___x_1084_; 
v___x_1084_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___redArg(v_x_1082_, v_x_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2___boxed(lean_object* v_00_u03b2_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
uint8_t v_res_1088_; lean_object* v_r_1089_; 
v_res_1088_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2(v_00_u03b2_1085_, v_x_1086_, v_x_1087_);
lean_dec(v_x_1087_);
lean_dec_ref(v_x_1086_);
v_r_1089_ = lean_box(v_res_1088_);
return v_r_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4(lean_object* v_00_u03b2_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4___redArg(v_x_1091_, v_x_1092_, v_x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(lean_object* v_00_u03b2_1095_, lean_object* v_x_1096_, size_t v_x_1097_, lean_object* v_x_1098_){
_start:
{
uint8_t v___x_1099_; 
v___x_1099_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___redArg(v_x_1096_, v_x_1097_, v_x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1100_, lean_object* v_x_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
size_t v_x_49301__boxed_1104_; uint8_t v_res_1105_; lean_object* v_r_1106_; 
v_x_49301__boxed_1104_ = lean_unbox_usize(v_x_1102_);
lean_dec(v_x_1102_);
v_res_1105_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5(v_00_u03b2_1100_, v_x_1101_, v_x_49301__boxed_1104_, v_x_1103_);
lean_dec(v_x_1103_);
lean_dec_ref(v_x_1101_);
v_r_1106_ = lean_box(v_res_1105_);
return v_r_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(lean_object* v_00_u03b2_1107_, lean_object* v_x_1108_, size_t v_x_1109_, size_t v_x_1110_, lean_object* v_x_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___redArg(v_x_1108_, v_x_1109_, v_x_1110_, v_x_1111_, v_x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
size_t v_x_49312__boxed_1120_; size_t v_x_49313__boxed_1121_; lean_object* v_res_1122_; 
v_x_49312__boxed_1120_ = lean_unbox_usize(v_x_1116_);
lean_dec(v_x_1116_);
v_x_49313__boxed_1121_ = lean_unbox_usize(v_x_1117_);
lean_dec(v_x_1117_);
v_res_1122_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8(v_00_u03b2_1114_, v_x_1115_, v_x_49312__boxed_1120_, v_x_49313__boxed_1121_, v_x_1118_, v_x_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1123_, lean_object* v_keys_1124_, lean_object* v_vals_1125_, lean_object* v_heq_1126_, lean_object* v_i_1127_, lean_object* v_k_1128_){
_start:
{
uint8_t v___x_1129_; 
v___x_1129_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_keys_1124_, v_i_1127_, v_k_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1130_, lean_object* v_keys_1131_, lean_object* v_vals_1132_, lean_object* v_heq_1133_, lean_object* v_i_1134_, lean_object* v_k_1135_){
_start:
{
uint8_t v_res_1136_; lean_object* v_r_1137_; 
v_res_1136_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__2_spec__2_spec__5_spec__8(v_00_u03b2_1130_, v_keys_1131_, v_vals_1132_, v_heq_1133_, v_i_1134_, v_k_1135_);
lean_dec(v_k_1135_);
lean_dec_ref(v_vals_1132_);
lean_dec_ref(v_keys_1131_);
v_r_1137_ = lean_box(v_res_1136_);
return v_r_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_1138_, lean_object* v_n_1139_, lean_object* v_k_1140_, lean_object* v_v_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11___redArg(v_n_1139_, v_k_1140_, v_v_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_1143_, size_t v_depth_1144_, lean_object* v_keys_1145_, lean_object* v_vals_1146_, lean_object* v_heq_1147_, lean_object* v_i_1148_, lean_object* v_entries_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___redArg(v_depth_1144_, v_keys_1145_, v_vals_1146_, v_i_1148_, v_entries_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1151_, lean_object* v_depth_1152_, lean_object* v_keys_1153_, lean_object* v_vals_1154_, lean_object* v_heq_1155_, lean_object* v_i_1156_, lean_object* v_entries_1157_){
_start:
{
size_t v_depth_boxed_1158_; lean_object* v_res_1159_; 
v_depth_boxed_1158_ = lean_unbox_usize(v_depth_1152_);
lean_dec(v_depth_1152_);
v_res_1159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__12(v_00_u03b2_1151_, v_depth_boxed_1158_, v_keys_1153_, v_vals_1154_, v_heq_1155_, v_i_1156_, v_entries_1157_);
lean_dec_ref(v_vals_1154_);
lean_dec_ref(v_keys_1153_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_x_1164_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Theorem_rewrite_spec__3_spec__4_spec__8_spec__11_spec__12___redArg(v_x_1161_, v_x_1162_, v_x_1163_, v_x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(lean_object* v_fst_1166_, lean_object* v_d_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1166_, v_x_1168_, v_d_1167_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed(lean_object* v_fst_1180_, lean_object* v_d_1181_, lean_object* v_x_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0(v_fst_1180_, v_d_1181_, v_x_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(lean_object* v_d_1194_, lean_object* v_e_1195_, lean_object* v_as_1196_, size_t v_sz_1197_, size_t v_i_1198_, lean_object* v_b_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v___y_1211_; lean_object* v___y_1212_; lean_object* v___y_1218_; uint8_t v___y_1219_; uint8_t v___y_1220_; lean_object* v___y_1223_; uint8_t v___y_1224_; uint8_t v___y_1225_; uint8_t v___y_1226_; lean_object* v___y_1228_; uint8_t v___y_1229_; uint8_t v___y_1230_; lean_object* v___y_1234_; uint8_t v___y_1235_; uint8_t v___x_1237_; 
v___x_1237_ = lean_usize_dec_lt(v_i_1198_, v_sz_1197_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; 
lean_dec_ref(v_e_1195_);
lean_dec_ref(v_d_1194_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v_b_1199_);
return v___x_1238_;
}
else
{
lean_object* v_a_1239_; lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1291_; 
v_a_1239_ = lean_array_uget_borrowed(v_as_1196_, v_i_1198_);
v_fst_1240_ = lean_ctor_get(v_a_1239_, 0);
v_snd_1241_ = lean_ctor_get(v_a_1239_, 1);
v_snd_1242_ = lean_ctor_get(v_b_1199_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_b_1199_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; 
v_unused_1292_ = lean_ctor_get(v_b_1199_, 0);
lean_dec(v_unused_1292_);
v___x_1244_ = v_b_1199_;
v_isShared_1245_ = v_isSharedCheck_1291_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_dec(v_b_1199_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1291_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1246_; lean_object* v___y_1248_; uint8_t v_done_1249_; uint8_t v___y_1250_; lean_object* v_result_1260_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1246_ = lean_box(0);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_nat_dec_eq(v_snd_1241_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___f_1270_; lean_object* v___x_1271_; 
lean_inc_ref(v_d_1194_);
lean_inc(v_fst_1240_);
v___f_1270_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___lam__0___boxed), 13, 2);
lean_closure_set(v___f_1270_, 0, v_fst_1240_);
lean_closure_set(v___f_1270_, 1, v_d_1194_);
lean_inc_ref(v_e_1195_);
v___x_1271_ = l_Lean_Meta_Sym_Simp_simpOverApplied(v_e_1195_, v_snd_1241_, v___f_1270_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v_result_1260_ = v_a_1272_;
goto v___jp_1259_;
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_del_object(v___x_1244_);
lean_dec(v_snd_1242_);
lean_dec_ref(v_e_1195_);
lean_dec_ref(v_d_1194_);
v_a_1273_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1271_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1271_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v___x_1281_; 
lean_inc_ref(v_d_1194_);
lean_inc_ref(v_e_1195_);
lean_inc(v_fst_1240_);
v___x_1281_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_fst_1240_, v_e_1195_, v_d_1194_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v_a_1282_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_a_1282_);
lean_dec_ref_known(v___x_1281_, 1);
v_result_1260_ = v_a_1282_;
goto v___jp_1259_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1244_);
lean_dec(v_snd_1242_);
lean_dec_ref(v_e_1195_);
lean_dec_ref(v_d_1194_);
v_a_1283_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1281_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
v___jp_1247_:
{
if (v_done_1249_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1253_; 
lean_dec_ref(v___y_1248_);
v___x_1251_ = lean_box(v___y_1250_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1251_);
lean_ctor_set(v___x_1244_, 0, v___x_1246_);
v___x_1253_ = v___x_1244_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
size_t v___x_1254_; size_t v___x_1255_; 
v___x_1254_ = ((size_t)1ULL);
v___x_1255_ = lean_usize_add(v_i_1198_, v___x_1254_);
v_i_1198_ = v___x_1255_;
v_b_1199_ = v___x_1253_;
goto _start;
}
}
else
{
uint8_t v___x_1258_; 
lean_del_object(v___x_1244_);
lean_dec_ref(v_e_1195_);
lean_dec_ref(v_d_1194_);
v___x_1258_ = 0;
v___y_1228_ = v___y_1248_;
v___y_1229_ = v___y_1250_;
v___y_1230_ = v___x_1258_;
goto v___jp_1227_;
}
}
v___jp_1259_:
{
uint8_t v___x_1261_; 
v___x_1261_ = lean_unbox(v_snd_1242_);
if (v___x_1261_ == 0)
{
lean_dec(v_snd_1242_);
if (lean_obj_tag(v_result_1260_) == 0)
{
uint8_t v_done_1262_; uint8_t v_contextDependent_1263_; 
v_done_1262_ = lean_ctor_get_uint8(v_result_1260_, 0);
v_contextDependent_1263_ = lean_ctor_get_uint8(v_result_1260_, 1);
v___y_1248_ = v_result_1260_;
v_done_1249_ = v_done_1262_;
v___y_1250_ = v_contextDependent_1263_;
goto v___jp_1247_;
}
else
{
uint8_t v_contextDependent_1264_; 
lean_del_object(v___x_1244_);
lean_dec_ref(v_e_1195_);
lean_dec_ref(v_d_1194_);
v_contextDependent_1264_ = lean_ctor_get_uint8(v_result_1260_, sizeof(void*)*2 + 1);
v___y_1234_ = v_result_1260_;
v___y_1235_ = v_contextDependent_1264_;
goto v___jp_1233_;
}
}
else
{
if (lean_obj_tag(v_result_1260_) == 0)
{
uint8_t v_done_1265_; uint8_t v___x_1266_; 
v_done_1265_ = lean_ctor_get_uint8(v_result_1260_, 0);
v___x_1266_ = lean_unbox(v_snd_1242_);
lean_dec(v_snd_1242_);
v___y_1248_ = v_result_1260_;
v_done_1249_ = v_done_1265_;
v___y_1250_ = v___x_1266_;
goto v___jp_1247_;
}
else
{
uint8_t v___x_1267_; 
lean_del_object(v___x_1244_);
lean_dec_ref(v_e_1195_);
lean_dec_ref(v_d_1194_);
v___x_1267_ = lean_unbox(v_snd_1242_);
lean_dec(v_snd_1242_);
v___y_1234_ = v_result_1260_;
v___y_1235_ = v___x_1267_;
goto v___jp_1233_;
}
}
}
}
}
v___jp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___y_1212_);
v___x_1214_ = lean_box(v___y_1211_);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1215_);
return v___x_1216_;
}
v___jp_1217_:
{
if (v___y_1220_ == 0)
{
v___y_1211_ = v___y_1219_;
v___y_1212_ = v___y_1218_;
goto v___jp_1210_;
}
else
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1218_);
v___y_1211_ = v___y_1219_;
v___y_1212_ = v___x_1221_;
goto v___jp_1210_;
}
}
v___jp_1222_:
{
if (v___y_1226_ == 0)
{
v___y_1218_ = v___y_1223_;
v___y_1219_ = v___y_1224_;
v___y_1220_ = v___y_1224_;
goto v___jp_1217_;
}
else
{
v___y_1218_ = v___y_1223_;
v___y_1219_ = v___y_1224_;
v___y_1220_ = v___y_1225_;
goto v___jp_1217_;
}
}
v___jp_1227_:
{
if (v___y_1229_ == 0)
{
v___y_1211_ = v___y_1229_;
v___y_1212_ = v___y_1228_;
goto v___jp_1210_;
}
else
{
if (lean_obj_tag(v___y_1228_) == 0)
{
uint8_t v_contextDependent_1231_; 
v_contextDependent_1231_ = lean_ctor_get_uint8(v___y_1228_, 1);
v___y_1223_ = v___y_1228_;
v___y_1224_ = v___y_1229_;
v___y_1225_ = v___y_1230_;
v___y_1226_ = v_contextDependent_1231_;
goto v___jp_1222_;
}
else
{
uint8_t v_contextDependent_1232_; 
v_contextDependent_1232_ = lean_ctor_get_uint8(v___y_1228_, sizeof(void*)*2 + 1);
v___y_1223_ = v___y_1228_;
v___y_1224_ = v___y_1229_;
v___y_1225_ = v___y_1230_;
v___y_1226_ = v_contextDependent_1232_;
goto v___jp_1222_;
}
}
}
v___jp_1233_:
{
uint8_t v___x_1236_; 
v___x_1236_ = 0;
v___y_1228_ = v___y_1234_;
v___y_1229_ = v___y_1235_;
v___y_1230_ = v___x_1236_;
goto v___jp_1227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0___boxed(lean_object* v_d_1293_, lean_object* v_e_1294_, lean_object* v_as_1295_, lean_object* v_sz_1296_, lean_object* v_i_1297_, lean_object* v_b_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
size_t v_sz_boxed_1309_; size_t v_i_boxed_1310_; lean_object* v_res_1311_; 
v_sz_boxed_1309_ = lean_unbox_usize(v_sz_1296_);
lean_dec(v_sz_1296_);
v_i_boxed_1310_ = lean_unbox_usize(v_i_1297_);
lean_dec(v_i_1297_);
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1293_, v_e_1294_, v_as_1295_, v_sz_boxed_1309_, v_i_boxed_1310_, v_b_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v_as_1295_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object* v_thms_1316_, lean_object* v_d_1317_, lean_object* v_e_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; size_t v_sz_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
v___x_1329_ = l_Lean_Meta_Sym_Simp_Theorems_getMatchWithExtra(v_thms_1316_, v_e_1318_);
v___x_1330_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Theorems_rewrite___closed__0));
v_sz_1331_ = lean_array_size(v___x_1329_);
v___x_1332_ = ((size_t)0ULL);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Sym_Simp_Theorems_rewrite_spec__0(v_d_1317_, v_e_1318_, v___x_1329_, v_sz_1331_, v___x_1332_, v___x_1330_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec_ref(v___x_1329_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1349_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1349_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1349_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v_fst_1338_; 
v_fst_1338_ = lean_ctor_get(v_a_1334_, 0);
if (lean_obj_tag(v_fst_1338_) == 0)
{
lean_object* v_snd_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
v_snd_1339_ = lean_ctor_get(v_a_1334_, 1);
lean_inc(v_snd_1339_);
lean_dec(v_a_1334_);
v___x_1340_ = lean_unbox(v_snd_1339_);
lean_dec(v_snd_1339_);
v___x_1341_ = l_Lean_Meta_Sym_Simp_mkRflResultCD(v___x_1340_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1341_);
v___x_1343_ = v___x_1336_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
else
{
lean_object* v_val_1345_; lean_object* v___x_1347_; 
lean_inc_ref(v_fst_1338_);
lean_dec(v_a_1334_);
v_val_1345_ = lean_ctor_get(v_fst_1338_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v_fst_1338_, 1);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v_val_1345_);
v___x_1347_ = v___x_1336_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_val_1345_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
v_a_1350_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1333_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1333_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite___boxed(lean_object* v_thms_1358_, lean_object* v_d_1359_, lean_object* v_e_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_thms_1358_, v_d_1359_, v_e_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_thms_1358_);
return v_res_1371_;
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
