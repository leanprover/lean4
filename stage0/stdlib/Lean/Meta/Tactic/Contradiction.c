// Lean compiler output
// Module: Lean.Meta.Tactic.Contradiction
// Imports: public import Lean.Meta.Tactic.Assumption public import Lean.Meta.Tactic.Cases public import Lean.Meta.Tactic.Apply import Lean.Meta.HasNotBit import Lean.Meta.Tactic.Simp.Rewrite
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
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 114, 54, 50, 40, 156, 62, 47)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2_value;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0_value;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0_value;
lean_object* l_Lean_Meta_saveState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_saveState___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1_value;
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1_value)} };
static const lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2_value;
static const lean_ctor_object l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2_value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0_value)}};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__2_value;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0_value;
static const lean_array_object l_Lean_Meta_ElimEmptyInductive_elim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__0 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "contradiction"};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__3 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__3_value;
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__2 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__2_value;
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__1 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__3_value),LEAN_SCALAR_PTR_LITERAL(100, 147, 90, 76, 177, 67, 155, 92)}};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__4 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value;
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "elimEmptyInductive, number subgoals: "};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1;
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "elimEmptyInductive out-of-fuel"};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__5 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__5_value;
static lean_once_cell_t l_Lean_Meta_ElimEmptyInductive_elim___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__6;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_mkGenDiseqMask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkGenDiseqMask___closed__0 = (const lean_object*)&l_Lean_Meta_mkGenDiseqMask___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0_value;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__1 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__2 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__3 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__4 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.MetavarContext"};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__0 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__0_value;
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.isLevelMVarAssignable"};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__1 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__1_value;
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "unknown universe metavariable "};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__2 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__2_value;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.Tactic.Contradiction"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Meta.Tactic.Contradiction.0.Lean.Meta.processGenDiseq"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "assertion violation: isGenDiseq localDecl.type\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3;
lean_object* l_Lean_LocalDecl_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0_value;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "of_decide_eq_false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(101, 242, 48, 138, 187, 4, 117, 248)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_refutableHasNotBit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchNe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchNot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MVarId_contradictionCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 42, 230, 185, 74, 16, 247, 90)}};
static const lean_object* l_Lean_MVarId_contradictionCore___closed__0 = (const lean_object*)&l_Lean_MVarId_contradictionCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Contradiction"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 99, 155, 115, 190, 254, 84, 130)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(215, 241, 81, 7, 129, 11, 88, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 199, 235, 149, 198, 6, 20, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 78, 37, 212, 63, 127, 41, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 88, 171, 83, 172, 77, 248, 159)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 220, 174, 134, 139, 23, 35, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 173, 142, 211, 165, 86, 65, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 154, 136, 66, 43, 95, 3, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__2_value),LEAN_SCALAR_PTR_LITERAL(142, 18, 4, 159, 144, 239, 124, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 255, 49, 161, 212, 67, 91, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)(((size_t)(911661800) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(54, 37, 52, 164, 114, 188, 198, 209)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 78, 196, 57, 182, 60, 174, 81)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 112, 60, 29, 144, 20, 193, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(84, 54, 65, 98, 52, 12, 188, 139)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2));
x_3 = lean_unsigned_to_nat(2u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_appArg_x21(x_1);
x_6 = l_Lean_Expr_hasLooseBVars(x_5);
lean_dec_ref(x_5);
if (x_6 == 0)
{
return x_4;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = l_Lean_instBEqMVarId_beq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = l_Lean_instBEqMVarId_beq(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__2);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_instHashableMVarId_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_instHashableMVarId_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_37; 
x_5 = lean_st_ref_take(x_3);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = lean_ctor_get(x_5, 4);
x_37 = !lean_is_exclusive(x_5);
if (x_37 == 0)
{
x_11 = x_5;
x_12 = x_37;
goto block_36;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_35; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
x_17 = lean_ctor_get(x_6, 4);
x_18 = lean_ctor_get(x_6, 5);
x_19 = lean_ctor_get(x_6, 6);
x_20 = lean_ctor_get(x_6, 7);
x_21 = lean_ctor_get(x_6, 8);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
x_22 = x_6;
x_23 = x_35;
goto block_34;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_22 = lean_box(0);
x_23 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(x_20, x_1, x_2);
if (x_23 == 0)
{
lean_ctor_set(x_22, 7, x_24);
x_25 = x_22;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_14);
lean_ctor_set(x_33, 2, x_15);
lean_ctor_set(x_33, 3, x_16);
lean_ctor_set(x_33, 4, x_17);
lean_ctor_set(x_33, 5, x_18);
lean_ctor_set(x_33, 6, x_19);
lean_ctor_set(x_33, 7, x_24);
lean_ctor_set(x_33, 8, x_21);
x_25 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_26; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_25);
x_26 = x_11;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_7);
lean_ctor_set(x_31, 2, x_8);
lean_ctor_set(x_31, 3, x_9);
lean_ctor_set(x_31, 4, x_10);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_st_ref_set(x_3, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_52; 
x_8 = lean_ctor_get(x_7, 0);
x_52 = !lean_is_exclusive(x_7);
if (x_52 == 0)
{
x_9 = x_7;
x_10 = x_52;
goto block_51;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_11; lean_object* x_12; 
x_11 = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
x_12 = lean_find_expr(x_11, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_del_object(x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_1);
x_14 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
lean_inc(x_3);
x_17 = l_Lean_Meta_mkFalseElim(x_15, x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_28; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_18, x_3);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_19, 0);
lean_dec(x_29);
x_20 = x_19;
x_21 = x_28;
goto block_27;
}
else
{
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = x_28;
goto block_27;
}
block_27:
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 1;
x_23 = lean_box(x_22);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_23);
x_24 = x_20;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_ctor_get(x_17, 0);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
x_31 = x_17;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_38 = lean_ctor_get(x_14, 0);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
x_39 = x_14;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_46 = 0;
x_47 = lean_box(x_46);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_47);
x_48 = x_9;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_47);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_7, 0);
x_60 = !lean_is_exclusive(x_7);
if (x_60 == 0)
{
x_54 = x_7;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_7);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_2, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_12; 
lean_inc_ref(x_2);
x_12 = l_Lean_FVarId_getType___redArg(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_5);
x_14 = l_Lean_Meta_whnfD(x_13, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_41; 
x_15 = lean_ctor_get(x_14, 0);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
x_16 = x_14;
x_17 = x_41;
goto block_40;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_18; 
x_18 = l_Lean_Expr_getAppFn(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 4)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_st_ref_get(x_5);
lean_dec(x_5);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Lean_Environment_find_x3f(x_21, x_19, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_del_object(x_16);
x_7 = lean_box(0);
goto block_11;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
if (lean_obj_tag(x_24) == 5)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 4);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = l_List_lengthTR___redArg(x_27);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_nat_dec_lt(x_29, x_26);
lean_dec(x_26);
x_32 = lean_box(x_31);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_32);
x_33 = x_16;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_26);
x_36 = lean_box(x_30);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_36);
x_37 = x_16;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_dec(x_24);
lean_del_object(x_16);
x_7 = lean_box(0);
goto block_11;
}
}
}
else
{
lean_dec_ref(x_18);
lean_del_object(x_16);
lean_dec(x_5);
x_7 = lean_box(0);
goto block_11;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_5);
x_42 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_43 = x_14;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_14);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_50 = lean_ctor_get(x_12, 0);
x_57 = !lean_is_exclusive(x_12);
if (x_57 == 0)
{
x_51 = x_12;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_12);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
block_11:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SavedState_restore___redArg(x_1, x_4, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed), 7, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_9, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_11 = lean_ctor_get(x_10, 0);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
x_12 = x_10;
x_13 = x_18;
goto block_17;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(x_1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_saveState___redArg(x_4, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_38; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_38 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec_ref(x_38);
x_41 = l_Lean_Meta_SavedState_restore___redArg(x_9, x_4, x_6);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_41, 0);
lean_dec(x_49);
x_42 = x_41;
x_43 = x_48;
goto block_47;
}
else
{
lean_dec(x_41);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
lean_ctor_set(x_42, 0, x_39);
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_39);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_39);
x_50 = lean_ctor_get(x_41, 0);
x_57 = !lean_is_exclusive(x_41);
if (x_57 == 0)
{
x_51 = x_41;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
lean_inc(x_50);
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
x_32 = x_53;
x_33 = x_50;
x_34 = lean_box(0);
goto block_37;
}
}
}
}
else
{
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_38;
}
}
else
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_38, 0);
lean_inc(x_58);
x_32 = x_38;
x_33 = x_58;
x_34 = lean_box(0);
goto block_37;
}
block_31:
{
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_11);
x_14 = l_Lean_Meta_SavedState_restore___redArg(x_9, x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; uint8_t x_21; 
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_15 = x_14;
x_16 = x_21;
goto block_20;
}
else
{
lean_dec(x_14);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_12);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_12);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec_ref(x_12);
x_23 = lean_ctor_get(x_14, 0);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
x_24 = x_14;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
else
{
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_11;
}
}
block_37:
{
uint8_t x_35; 
x_35 = l_Lean_Exception_isInterrupt(x_33);
if (x_35 == 0)
{
uint8_t x_36; 
lean_inc_ref(x_33);
x_36 = l_Lean_Exception_isRuntime(x_33);
x_10 = lean_box(0);
x_11 = x_32;
x_12 = x_33;
x_13 = x_36;
goto block_31;
}
else
{
x_10 = lean_box(0);
x_11 = x_32;
x_12 = x_33;
x_13 = x_35;
goto block_31;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_8, 0);
x_66 = !lean_is_exclusive(x_8);
if (x_66 == 0)
{
x_60 = x_8;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_8);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_53; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4_spec__4(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
x_11 = x_9;
x_12 = x_53;
goto block_52;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_13 = lean_st_ref_take(x_6);
x_14 = lean_ctor_get(x_13, 4);
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
x_18 = lean_ctor_get(x_13, 3);
x_19 = lean_ctor_get(x_13, 5);
x_20 = lean_ctor_get(x_13, 6);
x_21 = lean_ctor_get(x_13, 7);
x_22 = lean_ctor_get(x_13, 8);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
x_23 = x_13;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_14);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
uint64_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_49; 
x_25 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_26 = lean_ctor_get(x_14, 0);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
x_27 = x_14;
x_28 = x_49;
goto block_48;
}
else
{
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = x_49;
goto block_48;
}
block_48:
{
double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___closed__2));
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_10);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_26, x_35);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_36);
x_37 = x_27;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_25);
x_37 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_38; 
if (x_24 == 0)
{
lean_ctor_set(x_23, 4, x_37);
x_38 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_15);
lean_ctor_set(x_45, 1, x_16);
lean_ctor_set(x_45, 2, x_17);
lean_ctor_set(x_45, 3, x_18);
lean_ctor_set(x_45, 4, x_37);
lean_ctor_set(x_45, 5, x_19);
lean_ctor_set(x_45, 6, x_20);
lean_ctor_set(x_45, 7, x_21);
lean_ctor_set(x_45, 8, x_22);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_st_ref_set(x_6, x_38);
x_40 = lean_box(0);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_40);
x_41 = x_11;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox(x_7);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(x_1, x_2, x_3, x_14, x_15, x_6, x_16, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_55; 
lean_dec_ref(x_5);
x_14 = lean_array_uget(x_2, x_4);
x_15 = lean_ctor_get(x_14, 0);
x_55 = !lean_is_exclusive(x_14);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_14, 1);
lean_dec(x_56);
x_16 = x_14;
x_17 = x_55;
goto block_54;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_19);
x_20 = lean_box(0);
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_1, x_22);
x_24 = lean_array_size(x_19);
x_25 = lean_box_usize(x_24);
x_26 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
x_27 = lean_box(x_23);
lean_inc(x_18);
x_28 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(x_28, 0, x_15);
lean_closure_set(x_28, 1, x_18);
lean_closure_set(x_28, 2, x_19);
lean_closure_set(x_28, 3, x_25);
lean_closure_set(x_28, 4, x_26);
lean_closure_set(x_28, 5, x_21);
lean_closure_set(x_28, 6, x_27);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
x_29 = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(x_18, x_28, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_45; 
x_30 = lean_ctor_get(x_29, 0);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
x_31 = x_29;
x_32 = x_45;
goto block_44;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_45;
goto block_44;
}
block_44:
{
uint8_t x_33; 
x_33 = lean_unbox(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_30);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_20);
lean_ctor_set(x_16, 0, x_34);
x_35 = x_16;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_20);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_32 == 0)
{
lean_ctor_set(x_31, 0, x_35);
x_36 = x_31;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
else
{
size_t x_41; size_t x_42; 
lean_del_object(x_31);
lean_dec(x_30);
lean_del_object(x_16);
x_41 = 1;
x_42 = lean_usize_add(x_4, x_41);
x_4 = x_42;
x_5 = x_21;
goto _start;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_del_object(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_46 = lean_ctor_get(x_29, 0);
x_53 = !lean_is_exclusive(x_29);
if (x_53 == 0)
{
x_47 = x_29;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_29);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
x_13 = l_Lean_MVarId_cases(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_49; lean_object* x_50; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_49 = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
x_50 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(x_49, x_10);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_73; 
x_51 = lean_ctor_get(x_50, 0);
x_73 = !lean_is_exclusive(x_50);
if (x_73 == 0)
{
x_52 = x_50;
x_53 = x_73;
goto block_72;
}
else
{
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_box(0);
x_53 = x_73;
goto block_72;
}
block_72:
{
uint8_t x_54; 
x_54 = lean_unbox(x_51);
lean_dec(x_51);
if (x_54 == 0)
{
lean_del_object(x_52);
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
x_56 = lean_array_get_size(x_14);
x_57 = l_Nat_reprFast(x_56);
if (x_53 == 0)
{
lean_ctor_set_tag(x_52, 3);
lean_ctor_set(x_52, 0, x_57);
x_58 = x_52;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_57);
x_58 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = l_Lean_MessageData_ofFormat(x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_49, x_60, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
x_20 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_62 = lean_ctor_get(x_61, 0);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
x_63 = x_61;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_50;
}
block_48:
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
x_22 = lean_array_size(x_14);
x_23 = 0;
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(x_6, x_14, x_22, x_23, x_21, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_39; 
x_25 = lean_ctor_get(x_24, 0);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
x_26 = x_24;
x_27 = x_39;
goto block_38;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 1;
x_30 = lean_box(x_29);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_30);
x_31 = x_26;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec_ref(x_28);
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_34);
x_35 = x_26;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
x_40 = lean_ctor_get(x_24, 0);
x_47 = !lean_is_exclusive(x_24);
if (x_47 == 0)
{
x_41 = x_24;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_24);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_116; 
lean_dec(x_7);
x_74 = lean_ctor_get(x_13, 0);
x_116 = !lean_is_exclusive(x_13);
if (x_116 == 0)
{
x_75 = x_13;
x_76 = x_116;
goto block_115;
}
else
{
lean_inc(x_74);
lean_dec(x_13);
x_75 = lean_box(0);
x_76 = x_116;
goto block_115;
}
block_115:
{
uint8_t x_77; uint8_t x_113; 
x_113 = l_Lean_Exception_isInterrupt(x_74);
if (x_113 == 0)
{
uint8_t x_114; 
lean_inc(x_74);
x_114 = l_Lean_Exception_isRuntime(x_74);
x_77 = x_114;
goto block_112;
}
else
{
x_77 = x_113;
goto block_112;
}
block_112:
{
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_del_object(x_75);
x_78 = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
x_79 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(x_78, x_10);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_108; 
x_80 = lean_ctor_get(x_79, 0);
x_108 = !lean_is_exclusive(x_79);
if (x_108 == 0)
{
x_81 = x_79;
x_82 = x_108;
goto block_107;
}
else
{
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_box(0);
x_82 = x_108;
goto block_107;
}
block_107:
{
uint8_t x_83; 
x_83 = lean_unbox(x_80);
lean_dec(x_80);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_74);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_84 = lean_box(x_4);
if (x_82 == 0)
{
lean_ctor_set(x_81, 0, x_84);
x_85 = x_81;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_84);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_del_object(x_81);
x_88 = l_Lean_Exception_toMessageData(x_74);
x_89 = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_78, x_88, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; uint8_t x_97; 
x_97 = !lean_is_exclusive(x_89);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_89, 0);
lean_dec(x_98);
x_90 = x_89;
x_91 = x_97;
goto block_96;
}
else
{
lean_dec(x_89);
x_90 = lean_box(0);
x_91 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_box(x_4);
if (x_91 == 0)
{
lean_ctor_set(x_90, 0, x_92);
x_93 = x_90;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
x_99 = lean_ctor_get(x_89, 0);
x_106 = !lean_is_exclusive(x_89);
if (x_106 == 0)
{
x_100 = x_89;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_89);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
}
}
}
else
{
lean_dec(x_74);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_79;
}
}
else
{
lean_object* x_109; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (x_76 == 0)
{
x_109 = x_75;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_74);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
x_14 = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_st_ref_get(x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_st_ref_take(x_3);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = lean_st_ref_set(x_3, x_19);
x_21 = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
x_22 = lean_box(0);
x_23 = lean_box(x_16);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 12, 6);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_21);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_22);
lean_closure_set(x_24, 5, x_14);
x_25 = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5(x_24, x_3, x_4, x_5, x_6, x_7);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
x_27 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(x_26, x_6);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__6, &l_Lean_Meta_ElimEmptyInductive_elim___closed__6_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__6);
x_31 = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_26, x_30, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_31) == 0)
{
lean_dec_ref(x_31);
x_9 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
x_32 = lean_ctor_get(x_31, 0);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
x_33 = x_31;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_27;
}
}
block_13:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_5, x_4);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec_ref(x_6);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_box(0);
x_23 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
x_24 = lean_array_uget_borrowed(x_3, x_5);
lean_inc(x_21);
x_25 = l_Lean_Meta_FVarSubst_apply(x_21, x_24);
x_26 = l_Lean_Expr_isFVar(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
x_13 = x_23;
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec_ref(x_25);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_27);
x_28 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(x_27, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_dec(x_27);
x_13 = x_23;
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_31; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_31 = l_Lean_Meta_ElimEmptyInductive_elim(x_2, x_27, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_42; 
x_32 = lean_ctor_get(x_31, 0);
x_42 = !lean_is_exclusive(x_31);
if (x_42 == 0)
{
x_33 = x_31;
x_34 = x_42;
goto block_41;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_42;
goto block_41;
}
block_41:
{
uint8_t x_35; 
x_35 = lean_unbox(x_32);
if (x_35 == 0)
{
lean_del_object(x_33);
lean_dec(x_32);
x_13 = x_23;
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_22);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_37);
x_38 = x_33;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_31, 0);
x_50 = !lean_is_exclusive(x_31);
if (x_50 == 0)
{
x_44 = x_31;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_51 = lean_ctor_get(x_28, 0);
x_58 = !lean_is_exclusive(x_28);
if (x_58 == 0)
{
x_52 = x_28;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_28);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_5, x_15);
x_5 = x_16;
x_6 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_28; 
x_15 = lean_ctor_get(x_14, 0);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
x_16 = x_14;
x_17 = x_28;
goto block_27;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(x_7);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec_ref(x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_23);
x_24 = x_16;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
x_29 = lean_ctor_get(x_14, 0);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
x_30 = x_14;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_ElimEmptyInductive_elim(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_1, x_2, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_37 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_37);
x_40 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_40, 0);
lean_dec(x_48);
x_41 = x_40;
x_42 = x_47;
goto block_46;
}
else
{
lean_dec(x_40);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
lean_ctor_set(x_41, 0, x_38);
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_38);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_38);
x_49 = lean_ctor_get(x_40, 0);
x_56 = !lean_is_exclusive(x_40);
if (x_56 == 0)
{
x_50 = x_40;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
lean_inc(x_49);
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
x_31 = x_52;
x_32 = x_49;
x_33 = lean_box(0);
goto block_36;
}
}
}
}
else
{
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_37;
}
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_37, 0);
lean_inc(x_57);
x_31 = x_37;
x_32 = x_57;
x_33 = lean_box(0);
goto block_36;
}
block_30:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_9);
x_13 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_14 = x_13;
x_15 = x_20;
goto block_19;
}
else
{
lean_dec(x_13);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_11);
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_11);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec_ref(x_11);
x_22 = lean_ctor_get(x_13, 0);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
x_23 = x_13;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
else
{
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
block_36:
{
uint8_t x_34; 
x_34 = l_Lean_Exception_isInterrupt(x_32);
if (x_34 == 0)
{
uint8_t x_35; 
lean_inc_ref(x_32);
x_35 = l_Lean_Exception_isRuntime(x_32);
x_9 = x_31;
x_10 = lean_box(0);
x_11 = x_32;
x_12 = x_35;
goto block_30;
}
else
{
x_9 = x_31;
x_10 = lean_box(0);
x_11 = x_32;
x_12 = x_34;
goto block_30;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_58 = lean_ctor_get(x_7, 0);
x_65 = !lean_is_exclusive(x_7);
if (x_65 == 0)
{
x_59 = x_7;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_7);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_16; 
x_9 = lean_ctor_get(x_8, 0);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
x_10 = x_8;
x_11 = x_16;
goto block_15;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; 
if (x_11 == 0)
{
x_12 = x_10;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_17 = lean_ctor_get(x_8, 0);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
x_18 = x_8;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = l_Lean_MVarId_exfalso(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_st_mk_ref(x_2);
lean_inc(x_11);
x_12 = l_Lean_Meta_ElimEmptyInductive_elim(x_10, x_3, x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_21; 
x_13 = lean_ctor_get(x_12, 0);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
x_14 = x_12;
x_15 = x_21;
goto block_20;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_st_ref_get(x_11);
lean_dec(x_11);
lean_dec(x_16);
if (x_15 == 0)
{
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_13);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_dec(x_11);
return x_12;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_9, 0);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
x_23 = x_9;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_8 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
else
{
lean_object* x_11; 
lean_dec_ref(x_8);
x_11 = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(x_1, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_expr_has_loose_bvar(x_4, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isEq(x_3);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isHEq(x_3);
x_5 = x_13;
goto block_9;
}
else
{
x_5 = x_12;
goto block_9;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
x_5 = x_14;
goto block_9;
}
block_9:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(x_5);
x_7 = lean_array_push(x_2, x_6);
x_1 = x_4;
x_2 = x_7;
goto _start;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
x_3 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_mkGenDiseqMask(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_16 = x_11;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_10);
x_18 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
x_18 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_9);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), x_2, x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_16; 
x_9 = lean_ctor_get(x_8, 0);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
x_10 = x_8;
x_11 = x_16;
goto block_15;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; 
if (x_11 == 0)
{
x_12 = x_10;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_9);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_17 = lean_ctor_get(x_8, 0);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
x_18 = x_8;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l_Lean_instBEqLevelMVarId_beq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_4 = lean_ctor_get(x_1, 0);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
x_5 = x_1;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(2);
x_8 = 5;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get(x_7, x_4, x_11);
lean_dec(x_11);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_instBEqLevelMVarId_beq(x_3, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_del_object(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
x_17 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_del_object(x_5);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_del_object(x_5);
x_23 = lean_box(0);
return x_23;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(x_26, x_27, x_28, x_3);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_instHashableLevelMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_71; 
x_7 = lean_obj_once(&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0, &l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0_once, _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__0);
x_8 = l_ReaderT_instMonad___redArg(x_7);
x_9 = lean_ctor_get(x_8, 0);
x_71 = !lean_is_exclusive(x_8);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_8, 1);
lean_dec(x_72);
x_10 = x_8;
x_11 = x_71;
goto block_70;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_68; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 2);
x_14 = lean_ctor_get(x_9, 3);
x_15 = lean_ctor_get(x_9, 4);
x_68 = !lean_is_exclusive(x_9);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_9, 1);
lean_dec(x_69);
x_16 = x_9;
x_17 = x_68;
goto block_67;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__1));
x_19 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__2));
lean_inc_ref(x_12);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_12);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_12);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_15);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_14);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_13);
if (x_17 == 0)
{
lean_ctor_set(x_16, 4, x_23);
lean_ctor_set(x_16, 3, x_24);
lean_ctor_set(x_16, 2, x_25);
lean_ctor_set(x_16, 1, x_18);
lean_ctor_set(x_16, 0, x_22);
x_26 = x_16;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_66, 0, x_22);
lean_ctor_set(x_66, 1, x_18);
lean_ctor_set(x_66, 2, x_25);
lean_ctor_set(x_66, 3, x_24);
lean_ctor_set(x_66, 4, x_23);
x_26 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_27; 
if (x_11 == 0)
{
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_26);
x_27 = x_10;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_26);
lean_ctor_set(x_64, 1, x_19);
x_27 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_61; 
x_28 = l_ReaderT_instMonad___redArg(x_27);
x_29 = lean_ctor_get(x_28, 0);
x_61 = !lean_is_exclusive(x_28);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_28, 1);
lean_dec(x_62);
x_30 = x_28;
x_31 = x_61;
goto block_60;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_58; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = lean_ctor_get(x_29, 2);
x_34 = lean_ctor_get(x_29, 3);
x_35 = lean_ctor_get(x_29, 4);
x_58 = !lean_is_exclusive(x_29);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_29, 1);
lean_dec(x_59);
x_36 = x_29;
x_37 = x_58;
goto block_57;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__3));
x_39 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___closed__4));
lean_inc_ref(x_32);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_40, 0, x_32);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_35);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_44, 0, x_34);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_45, 0, x_33);
if (x_37 == 0)
{
lean_ctor_set(x_36, 4, x_43);
lean_ctor_set(x_36, 3, x_44);
lean_ctor_set(x_36, 2, x_45);
lean_ctor_set(x_36, 1, x_38);
lean_ctor_set(x_36, 0, x_42);
x_46 = x_36;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_42);
lean_ctor_set(x_56, 1, x_38);
lean_ctor_set(x_56, 2, x_45);
lean_ctor_set(x_56, 3, x_44);
lean_ctor_set(x_56, 4, x_43);
x_46 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_47; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_39);
lean_ctor_set(x_30, 0, x_46);
x_47 = x_30;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_39);
x_47 = x_54;
goto block_53;
}
block_53:
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = 0;
x_49 = lean_box(x_48);
x_50 = l_instInhabitedOfMonad___redArg(x_47, x_49);
x_51 = lean_panic_fn(x_50, x_1);
x_52 = lean_apply_5(x_51, x_2, x_3, x_4, x_5, lean_box(0));
return x_52;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_st_ref_get(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 3);
lean_inc_ref(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(x_10, x_1);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_21; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 0);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
x_13 = x_11;
x_14 = x_21;
goto block_20;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_21;
goto block_20;
}
block_20:
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_nat_dec_le(x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
x_16 = lean_box(x_15);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_16);
x_17 = x_13;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
lean_dec(x_9);
x_22 = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__0));
x_23 = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__1));
x_24 = lean_unsigned_to_nat(445u);
x_25 = lean_unsigned_to_nat(14u);
x_26 = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___closed__2));
x_27 = 1;
x_28 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_27);
x_29 = lean_string_append(x_26, x_28);
lean_dec_ref(x_28);
x_30 = l_mkPanicMessageWithDecl(x_22, x_23, x_24, x_25, x_29);
lean_dec_ref(x_29);
x_31 = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__8(x_30, x_2, x_3, x_4, x_5);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = l_Lean_Level_hasMVar(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
x_1 = x_25;
goto _start;
}
}
case 2:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec_ref(x_1);
x_16 = x_30;
x_17 = x_31;
goto block_24;
}
case 3:
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec_ref(x_1);
x_16 = x_32;
x_17 = x_33;
goto block_24;
}
case 5:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec_ref(x_1);
x_35 = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(x_34, x_2, x_3, x_4, x_5);
return x_35;
}
default: 
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_36 = 0;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
block_15:
{
if (x_9 == 0)
{
uint8_t x_11; 
lean_dec_ref(x_8);
x_11 = l_Lean_Level_hasMVar(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
block_24:
{
uint8_t x_18; 
x_18 = l_Lean_Level_hasMVar(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_7 = x_17;
x_8 = x_20;
x_9 = x_18;
x_10 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_21; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_21 = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
x_7 = x_17;
x_8 = x_21;
x_9 = x_23;
x_10 = lean_box(0);
goto block_15;
}
else
{
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec_ref(x_1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_12 = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(x_10, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec_ref(x_12);
x_1 = x_11;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
else
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
lean_inc_ref(x_5);
x_6 = l_Lean_MetavarContext_getDecl(x_5, x_1);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_16; lean_object* x_17; 
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec_ref(x_1);
x_26 = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(x_25, x_3);
lean_dec(x_3);
return x_26;
}
case 3:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec_ref(x_1);
x_28 = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(x_27, x_2, x_3, x_4, x_5);
return x_28;
}
case 4:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec_ref(x_1);
x_30 = l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(x_29, x_2, x_3, x_4, x_5);
return x_30;
}
case 5:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_41; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_32);
lean_dec_ref(x_1);
x_41 = l_Lean_Expr_hasMVar(x_31);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_31);
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_33 = x_43;
x_34 = x_41;
x_35 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_44; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_44 = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_31, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
x_33 = x_44;
x_34 = x_46;
x_35 = lean_box(0);
goto block_40;
}
else
{
lean_dec_ref(x_32);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_44;
}
}
block_40:
{
if (x_34 == 0)
{
uint8_t x_36; 
lean_dec_ref(x_33);
x_36 = l_Lean_Expr_hasMVar(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_32);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
else
{
x_1 = x_32;
goto _start;
}
}
else
{
lean_dec_ref(x_32);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_33;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_48);
lean_dec_ref(x_1);
x_16 = x_47;
x_17 = x_48;
goto block_24;
}
case 7:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_50);
lean_dec_ref(x_1);
x_16 = x_49;
x_17 = x_50;
goto block_24;
}
case 8:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_72; 
x_51 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_51);
x_52 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_52);
x_53 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_53);
lean_dec_ref(x_1);
x_72 = l_Lean_Expr_hasMVar(x_51);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_51);
x_73 = lean_box(x_72);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_62 = x_74;
x_63 = x_72;
x_64 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_75; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_75 = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_51, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
x_62 = x_75;
x_63 = x_77;
x_64 = lean_box(0);
goto block_71;
}
else
{
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_75;
}
}
block_61:
{
if (x_55 == 0)
{
uint8_t x_57; 
lean_dec_ref(x_54);
x_57 = l_Lean_Expr_hasMVar(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_53);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
else
{
x_1 = x_53;
goto _start;
}
}
else
{
lean_dec_ref(x_53);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_54;
}
}
block_71:
{
if (x_63 == 0)
{
uint8_t x_65; 
lean_dec_ref(x_62);
x_65 = l_Lean_Expr_hasMVar(x_52);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_52);
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_54 = x_67;
x_55 = x_65;
x_56 = lean_box(0);
goto block_61;
}
else
{
lean_object* x_68; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_68 = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_52, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
x_54 = x_68;
x_55 = x_70;
x_56 = lean_box(0);
goto block_61;
}
else
{
lean_dec_ref(x_53);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_68;
}
}
}
else
{
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_62;
}
}
}
case 10:
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_78);
lean_dec_ref(x_1);
x_79 = l_Lean_Expr_hasMVar(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_78);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_80 = lean_box(x_79);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
else
{
x_1 = x_78;
goto _start;
}
}
case 11:
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_83);
lean_dec_ref(x_1);
x_84 = l_Lean_Expr_hasMVar(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_83);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_85 = lean_box(x_84);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
else
{
x_1 = x_83;
goto _start;
}
}
default: 
{
uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_88 = 0;
x_89 = lean_box(x_88);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
block_15:
{
if (x_9 == 0)
{
uint8_t x_11; 
lean_dec_ref(x_8);
x_11 = l_Lean_Expr_hasMVar(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
block_24:
{
uint8_t x_18; 
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_16);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_7 = x_17;
x_8 = x_20;
x_9 = x_18;
x_10 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_21; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_21 = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_16, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
x_7 = x_17;
x_8 = x_21;
x_9 = x_23;
x_10 = lean_box(0);
goto block_15;
}
else
{
lean_dec_ref(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_3, x_2);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_176; 
x_18 = lean_ctor_get(x_4, 1);
x_176 = !lean_is_exclusive(x_4);
if (x_176 == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_4, 0);
lean_dec(x_177);
x_19 = x_4;
x_20 = x_176;
goto block_175;
}
else
{
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 2);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_22, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_24);
x_26 = x_19;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_18);
x_26 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
lean_object* x_30; uint8_t x_31; uint8_t x_171; 
lean_inc(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_171 = !lean_is_exclusive(x_18);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_18, 2);
lean_dec(x_172);
x_173 = lean_ctor_get(x_18, 1);
lean_dec(x_173);
x_174 = lean_ctor_get(x_18, 0);
lean_dec(x_174);
x_30 = x_18;
x_31 = x_171;
goto block_170;
}
else
{
lean_dec(x_18);
x_30 = lean_box(0);
x_31 = x_171;
goto block_170;
}
block_170:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_array_fget(x_21, x_22);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_22, x_33);
lean_dec(x_22);
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_34);
x_35 = x_30;
goto block_168;
}
else
{
lean_object* x_169; 
x_169 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_169, 0, x_21);
lean_ctor_set(x_169, 1, x_34);
lean_ctor_set(x_169, 2, x_23);
x_35 = x_169;
goto block_168;
}
block_168:
{
uint8_t x_36; 
x_36 = lean_unbox(x_32);
lean_dec(x_32);
if (x_36 == 0)
{
lean_object* x_37; 
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_35);
lean_ctor_set(x_19, 0, x_24);
x_37 = x_19;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_35);
x_37 = x_39;
goto block_38;
}
block_38:
{
x_10 = x_37;
x_11 = lean_box(0);
goto block_15;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_108; 
x_40 = lean_array_uget_borrowed(x_1, x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_40);
x_108 = lean_infer_type(x_40, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_110 = l_Lean_Meta_matchEq_x3f(x_109, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
if (lean_obj_tag(x_111) == 1)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_150; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_ctor_get(x_113, 0);
x_150 = !lean_is_exclusive(x_113);
if (x_150 == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_113, 1);
lean_dec(x_151);
x_115 = x_113;
x_116 = x_150;
goto block_149;
}
else
{
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_box(0);
x_116 = x_150;
goto block_149;
}
block_149:
{
lean_object* x_117; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_117 = l_Lean_Meta_mkEqRefl(x_114, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_40);
x_119 = l_Lean_Meta_isExprDefEq(x_40, x_118, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_132; 
x_120 = lean_ctor_get(x_119, 0);
x_132 = !lean_is_exclusive(x_119);
if (x_132 == 0)
{
x_121 = x_119;
x_122 = x_132;
goto block_131;
}
else
{
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_box(0);
x_122 = x_132;
goto block_131;
}
block_131:
{
uint8_t x_123; 
x_123 = lean_unbox(x_120);
lean_dec(x_120);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_del_object(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_124 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (x_116 == 0)
{
lean_ctor_set(x_115, 1, x_35);
lean_ctor_set(x_115, 0, x_124);
x_125 = x_115;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_35);
x_125 = x_130;
goto block_129;
}
block_129:
{
lean_object* x_126; 
if (x_122 == 0)
{
lean_ctor_set(x_121, 0, x_125);
x_126 = x_121;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_125);
x_126 = x_128;
goto block_127;
}
block_127:
{
return x_126;
}
}
}
else
{
lean_del_object(x_121);
lean_del_object(x_115);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_41 = x_5;
x_42 = x_6;
x_43 = x_7;
x_44 = x_8;
x_45 = lean_box(0);
goto block_107;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_140; 
lean_del_object(x_115);
lean_dec_ref(x_35);
lean_del_object(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_133 = lean_ctor_get(x_119, 0);
x_140 = !lean_is_exclusive(x_119);
if (x_140 == 0)
{
x_134 = x_119;
x_135 = x_140;
goto block_139;
}
else
{
lean_inc(x_133);
lean_dec(x_119);
x_134 = lean_box(0);
x_135 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_136; 
if (x_135 == 0)
{
x_136 = x_134;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_133);
x_136 = x_138;
goto block_137;
}
block_137:
{
return x_136;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_148; 
lean_del_object(x_115);
lean_dec_ref(x_35);
lean_del_object(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_141 = lean_ctor_get(x_117, 0);
x_148 = !lean_is_exclusive(x_117);
if (x_148 == 0)
{
x_142 = x_117;
x_143 = x_148;
goto block_147;
}
else
{
lean_inc(x_141);
lean_dec(x_117);
x_142 = lean_box(0);
x_143 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_144; 
if (x_143 == 0)
{
x_144 = x_142;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_141);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
}
}
}
else
{
lean_dec(x_111);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_41 = x_5;
x_42 = x_6;
x_43 = x_7;
x_44 = x_8;
x_45 = lean_box(0);
goto block_107;
}
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_159; 
lean_dec_ref(x_35);
lean_del_object(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_152 = lean_ctor_get(x_110, 0);
x_159 = !lean_is_exclusive(x_110);
if (x_159 == 0)
{
x_153 = x_110;
x_154 = x_159;
goto block_158;
}
else
{
lean_inc(x_152);
lean_dec(x_110);
x_153 = lean_box(0);
x_154 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_155; 
if (x_154 == 0)
{
x_155 = x_153;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_152);
x_155 = x_157;
goto block_156;
}
block_156:
{
return x_155;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; uint8_t x_167; 
lean_dec_ref(x_35);
lean_del_object(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_160 = lean_ctor_get(x_108, 0);
x_167 = !lean_is_exclusive(x_108);
if (x_167 == 0)
{
x_161 = x_108;
x_162 = x_167;
goto block_166;
}
else
{
lean_inc(x_160);
lean_dec(x_108);
x_161 = lean_box(0);
x_162 = x_167;
goto block_166;
}
block_166:
{
lean_object* x_163; 
if (x_162 == 0)
{
x_163 = x_161;
goto block_164;
}
else
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_160);
x_163 = x_165;
goto block_164;
}
block_164:
{
return x_163;
}
}
}
block_107:
{
lean_object* x_46; 
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
x_46 = lean_infer_type(x_40, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
x_48 = l_Lean_Meta_matchHEq_x3f(x_47, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
if (lean_obj_tag(x_49) == 1)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
x_53 = l_Lean_Meta_mkHEqRefl(x_52, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
lean_inc(x_40);
x_55 = l_Lean_Meta_isExprDefEq(x_40, x_54, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_71; 
x_56 = lean_ctor_get(x_55, 0);
x_71 = !lean_is_exclusive(x_55);
if (x_71 == 0)
{
x_57 = x_55;
x_58 = x_71;
goto block_70;
}
else
{
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = x_71;
goto block_70;
}
block_70:
{
uint8_t x_59; 
x_59 = lean_unbox(x_56);
lean_dec(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_60 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_35);
lean_ctor_set(x_19, 0, x_60);
x_61 = x_19;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_60);
lean_ctor_set(x_66, 1, x_35);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_58 == 0)
{
lean_ctor_set(x_57, 0, x_61);
x_62 = x_57;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_61);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
else
{
lean_object* x_67; 
lean_del_object(x_57);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_35);
lean_ctor_set(x_19, 0, x_24);
x_67 = x_19;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_24);
lean_ctor_set(x_69, 1, x_35);
x_67 = x_69;
goto block_68;
}
block_68:
{
x_10 = x_67;
x_11 = lean_box(0);
goto block_15;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec_ref(x_35);
lean_del_object(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_72 = lean_ctor_get(x_55, 0);
x_79 = !lean_is_exclusive(x_55);
if (x_79 == 0)
{
x_73 = x_55;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_55);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_87; 
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_35);
lean_del_object(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_80 = lean_ctor_get(x_53, 0);
x_87 = !lean_is_exclusive(x_53);
if (x_87 == 0)
{
x_81 = x_53;
x_82 = x_87;
goto block_86;
}
else
{
lean_inc(x_80);
lean_dec(x_53);
x_81 = lean_box(0);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
if (x_82 == 0)
{
x_83 = x_81;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_80);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
else
{
lean_object* x_88; 
lean_dec(x_49);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
if (x_20 == 0)
{
lean_ctor_set(x_19, 1, x_35);
lean_ctor_set(x_19, 0, x_24);
x_88 = x_19;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_24);
lean_ctor_set(x_90, 1, x_35);
x_88 = x_90;
goto block_89;
}
block_89:
{
x_10 = x_88;
x_11 = lean_box(0);
goto block_15;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_98; 
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_35);
lean_del_object(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_91 = lean_ctor_get(x_48, 0);
x_98 = !lean_is_exclusive(x_48);
if (x_98 == 0)
{
x_92 = x_48;
x_93 = x_98;
goto block_97;
}
else
{
lean_inc(x_91);
lean_dec(x_48);
x_92 = lean_box(0);
x_93 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_94; 
if (x_93 == 0)
{
x_94 = x_92;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_35);
lean_del_object(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_99 = lean_ctor_get(x_46, 0);
x_106 = !lean_is_exclusive(x_46);
if (x_106 == 0)
{
x_100 = x_46;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_46);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
}
}
}
}
}
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_10 = l_Lean_Meta_forallMetaTelescope(x_1, x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_101; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
x_101 = !lean_is_exclusive(x_11);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_11, 1);
lean_dec(x_102);
x_13 = x_11;
x_14 = x_101;
goto block_100;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = l_Lean_Meta_mkGenDiseqMask(x_1);
lean_dec_ref(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_15);
x_18 = l_Array_toSubarray___redArg(x_15, x_16, x_17);
x_19 = lean_box(0);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_18);
lean_ctor_set(x_13, 0, x_19);
x_20 = x_13;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_19);
lean_ctor_set(x_99, 1, x_18);
x_20 = x_99;
goto block_98;
}
block_98:
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_array_size(x_12);
x_22 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(x_12, x_21, x_22, x_20, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_89; 
x_24 = lean_ctor_get(x_23, 0);
x_89 = !lean_is_exclusive(x_23);
if (x_89 == 0)
{
x_25 = x_23;
x_26 = x_89;
goto block_88;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_83; 
lean_del_object(x_25);
x_28 = l_Lean_LocalDecl_toExpr(x_3);
x_29 = l_Lean_mkAppN(x_28, x_12);
lean_dec(x_12);
x_30 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_29, x_6);
x_31 = lean_ctor_get(x_30, 0);
x_83 = !lean_is_exclusive(x_30);
if (x_83 == 0)
{
x_32 = x_30;
x_33 = x_83;
goto block_82;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_34; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_31);
x_34 = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_31, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_73; 
x_35 = lean_ctor_get(x_34, 0);
x_73 = !lean_is_exclusive(x_34);
if (x_73 == 0)
{
x_36 = x_34;
x_37 = x_73;
goto block_72;
}
else
{
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = x_73;
goto block_72;
}
block_72:
{
uint8_t x_38; 
x_38 = lean_unbox(x_35);
lean_dec(x_35);
if (x_38 == 0)
{
lean_object* x_39; 
lean_del_object(x_36);
x_39 = l_Lean_MVarId_getType(x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Meta_mkFalseElim(x_40, x_31, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_52; 
x_42 = lean_ctor_get(x_41, 0);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
x_43 = x_41;
x_44 = x_52;
goto block_51;
}
else
{
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_45; 
if (x_33 == 0)
{
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_42);
x_45 = x_32;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_42);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_44 == 0)
{
lean_ctor_set(x_43, 0, x_45);
x_46 = x_43;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_del_object(x_32);
x_53 = lean_ctor_get(x_41, 0);
x_60 = !lean_is_exclusive(x_41);
if (x_60 == 0)
{
x_54 = x_41;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_41);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_del_object(x_32);
lean_dec(x_31);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_61 = lean_ctor_get(x_39, 0);
x_68 = !lean_is_exclusive(x_39);
if (x_68 == 0)
{
x_62 = x_39;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_39);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
else
{
lean_object* x_69; 
lean_del_object(x_32);
lean_dec(x_31);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
if (x_37 == 0)
{
lean_ctor_set(x_36, 0, x_19);
x_69 = x_36;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_19);
x_69 = x_71;
goto block_70;
}
block_70:
{
return x_69;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_81; 
lean_del_object(x_32);
lean_dec(x_31);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_74 = lean_ctor_get(x_34, 0);
x_81 = !lean_is_exclusive(x_34);
if (x_81 == 0)
{
x_75 = x_34;
x_76 = x_81;
goto block_80;
}
else
{
lean_inc(x_74);
lean_dec(x_34);
x_75 = lean_box(0);
x_76 = x_81;
goto block_80;
}
block_80:
{
lean_object* x_77; 
if (x_76 == 0)
{
x_77 = x_75;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_74);
x_77 = x_79;
goto block_78;
}
block_78:
{
return x_77;
}
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_84 = lean_ctor_get(x_27, 0);
lean_inc(x_84);
lean_dec_ref(x_27);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_84);
x_85 = x_25;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_84);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_97; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_90 = lean_ctor_get(x_23, 0);
x_97 = !lean_is_exclusive(x_23);
if (x_97 == 0)
{
x_91 = x_23;
x_92 = x_97;
goto block_96;
}
else
{
lean_inc(x_90);
lean_dec(x_23);
x_91 = lean_box(0);
x_92 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_93; 
if (x_92 == 0)
{
x_93 = x_91;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_90);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_110; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_103 = lean_ctor_get(x_10, 0);
x_110 = !lean_is_exclusive(x_10);
if (x_110 == 0)
{
x_104 = x_10;
x_105 = x_110;
goto block_109;
}
else
{
lean_inc(x_103);
lean_dec(x_10);
x_104 = lean_box(0);
x_105 = x_110;
goto block_109;
}
block_109:
{
lean_object* x_106; 
if (x_105 == 0)
{
x_106 = x_104;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_103);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(120u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_LocalDecl_type(x_2);
lean_inc_ref(x_8);
x_9 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
x_11 = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(x_10, x_3, x_4, x_5, x_6);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = 0;
x_13 = lean_box(x_12);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_1);
x_15 = 0;
lean_inc(x_4);
x_16 = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__4___redArg(x_14, x_15, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_36; 
x_17 = lean_ctor_get(x_16, 0);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_18 = x_16;
x_19 = x_36;
goto block_35;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_36;
goto block_35;
}
block_35:
{
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_29; 
lean_del_object(x_18);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec_ref(x_17);
x_21 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_1, x_20, x_4);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_21, 0);
lean_dec(x_30);
x_22 = x_21;
x_23 = x_29;
goto block_28;
}
else
{
lean_dec(x_21);
x_22 = lean_box(0);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(x_9);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_24);
x_25 = x_22;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_1);
x_31 = lean_box(x_15);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_31);
x_32 = x_18;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_31);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_4);
lean_dec(x_1);
x_37 = lean_ctor_get(x_16, 0);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
x_38 = x_16;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6_spec__7_spec__9_spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static uint64_t _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1(void) {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_704; 
x_14 = lean_ctor_get(x_6, 1);
x_704 = !lean_is_exclusive(x_6);
if (x_704 == 0)
{
lean_object* x_705; 
x_705 = lean_ctor_get(x_6, 0);
lean_dec(x_705);
x_15 = x_6;
x_16 = x_704;
goto block_703;
}
else
{
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_704;
goto block_703;
}
block_703:
{
lean_object* x_17; lean_object* x_18; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_33; 
x_25 = lean_box(0);
x_33 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_33) == 0)
{
lean_del_object(x_15);
x_26 = x_14;
x_27 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_702; 
x_34 = lean_ctor_get(x_33, 0);
x_702 = !lean_is_exclusive(x_33);
if (x_702 == 0)
{
x_35 = x_33;
x_36 = x_702;
goto block_701;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_702;
goto block_701;
}
block_701:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_37 = lean_box(0);
x_79 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
x_109 = l_Lean_LocalDecl_isImplementationDetail(x_34);
if (x_109 == 0)
{
lean_object* x_157; uint8_t x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_179; uint8_t x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_190; uint8_t x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_282; uint8_t x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_302; uint8_t x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_322; uint8_t x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; uint8_t x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_638; 
x_157 = l_Lean_LocalDecl_type(x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_157);
x_638 = l_Lean_Meta_matchNot_x3f(x_157, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
lean_dec_ref(x_638);
if (lean_obj_tag(x_639) == 1)
{
lean_object* x_640; lean_object* x_641; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
lean_dec_ref(x_639);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_641 = l_Lean_Meta_findLocalDeclWithType_x3f(x_640, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
lean_dec_ref(x_641);
if (lean_obj_tag(x_642) == 1)
{
lean_object* x_643; lean_object* x_644; uint8_t x_645; uint8_t x_684; 
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec_ref(x_1);
x_643 = lean_ctor_get(x_642, 0);
x_684 = !lean_is_exclusive(x_642);
if (x_684 == 0)
{
x_644 = x_642;
x_645 = x_684;
goto block_683;
}
else
{
lean_inc(x_643);
lean_dec(x_642);
x_644 = lean_box(0);
x_645 = x_684;
goto block_683;
}
block_683:
{
lean_object* x_646; 
lean_inc(x_2);
x_646 = l_Lean_MVarId_getType(x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
lean_dec_ref(x_646);
x_648 = l_Lean_LocalDecl_toExpr(x_34);
x_649 = l_Lean_mkFVar(x_643);
x_650 = l_Lean_Expr_app___override(x_648, x_649);
lean_inc(x_8);
x_651 = l_Lean_Meta_mkFalseElim(x_647, x_650, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
lean_dec_ref(x_651);
x_653 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_652, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; lean_object* x_655; 
lean_dec_ref(x_653);
x_654 = lean_box(x_12);
if (x_645 == 0)
{
lean_ctor_set(x_644, 0, x_654);
x_655 = x_644;
goto block_657;
}
else
{
lean_object* x_658; 
x_658 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_658, 0, x_654);
x_655 = x_658;
goto block_657;
}
block_657:
{
lean_object* x_656; 
x_656 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_37);
x_17 = x_656;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_659; lean_object* x_660; uint8_t x_661; uint8_t x_666; 
lean_del_object(x_644);
lean_del_object(x_15);
lean_dec(x_14);
x_659 = lean_ctor_get(x_653, 0);
x_666 = !lean_is_exclusive(x_653);
if (x_666 == 0)
{
x_660 = x_653;
x_661 = x_666;
goto block_665;
}
else
{
lean_inc(x_659);
lean_dec(x_653);
x_660 = lean_box(0);
x_661 = x_666;
goto block_665;
}
block_665:
{
lean_object* x_662; 
if (x_661 == 0)
{
x_662 = x_660;
goto block_663;
}
else
{
lean_object* x_664; 
x_664 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_664, 0, x_659);
x_662 = x_664;
goto block_663;
}
block_663:
{
return x_662;
}
}
}
}
else
{
lean_object* x_667; lean_object* x_668; uint8_t x_669; uint8_t x_674; 
lean_del_object(x_644);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
x_667 = lean_ctor_get(x_651, 0);
x_674 = !lean_is_exclusive(x_651);
if (x_674 == 0)
{
x_668 = x_651;
x_669 = x_674;
goto block_673;
}
else
{
lean_inc(x_667);
lean_dec(x_651);
x_668 = lean_box(0);
x_669 = x_674;
goto block_673;
}
block_673:
{
lean_object* x_670; 
if (x_669 == 0)
{
x_670 = x_668;
goto block_671;
}
else
{
lean_object* x_672; 
x_672 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_672, 0, x_667);
x_670 = x_672;
goto block_671;
}
block_671:
{
return x_670;
}
}
}
}
else
{
lean_object* x_675; lean_object* x_676; uint8_t x_677; uint8_t x_682; 
lean_del_object(x_644);
lean_dec(x_643);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_675 = lean_ctor_get(x_646, 0);
x_682 = !lean_is_exclusive(x_646);
if (x_682 == 0)
{
x_676 = x_646;
x_677 = x_682;
goto block_681;
}
else
{
lean_inc(x_675);
lean_dec(x_646);
x_676 = lean_box(0);
x_677 = x_682;
goto block_681;
}
block_681:
{
lean_object* x_678; 
if (x_677 == 0)
{
x_678 = x_676;
goto block_679;
}
else
{
lean_object* x_680; 
x_680 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_680, 0, x_675);
x_678 = x_680;
goto block_679;
}
block_679:
{
return x_678;
}
}
}
}
}
else
{
lean_dec(x_642);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_502 = x_7;
x_503 = x_8;
x_504 = x_9;
x_505 = x_10;
x_506 = lean_box(0);
goto block_637;
}
}
else
{
lean_object* x_685; lean_object* x_686; uint8_t x_687; uint8_t x_692; 
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_685 = lean_ctor_get(x_641, 0);
x_692 = !lean_is_exclusive(x_641);
if (x_692 == 0)
{
x_686 = x_641;
x_687 = x_692;
goto block_691;
}
else
{
lean_inc(x_685);
lean_dec(x_641);
x_686 = lean_box(0);
x_687 = x_692;
goto block_691;
}
block_691:
{
lean_object* x_688; 
if (x_687 == 0)
{
x_688 = x_686;
goto block_689;
}
else
{
lean_object* x_690; 
x_690 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_690, 0, x_685);
x_688 = x_690;
goto block_689;
}
block_689:
{
return x_688;
}
}
}
}
else
{
lean_dec(x_639);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_502 = x_7;
x_503 = x_8;
x_504 = x_9;
x_505 = x_10;
x_506 = lean_box(0);
goto block_637;
}
}
else
{
lean_object* x_693; lean_object* x_694; uint8_t x_695; uint8_t x_700; 
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_693 = lean_ctor_get(x_638, 0);
x_700 = !lean_is_exclusive(x_638);
if (x_700 == 0)
{
x_694 = x_638;
x_695 = x_700;
goto block_699;
}
else
{
lean_inc(x_693);
lean_dec(x_638);
x_694 = lean_box(0);
x_695 = x_700;
goto block_699;
}
block_699:
{
lean_object* x_696; 
if (x_695 == 0)
{
x_696 = x_694;
goto block_697;
}
else
{
lean_object* x_698; 
x_698 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_698, 0, x_693);
x_696 = x_698;
goto block_697;
}
block_697:
{
return x_696;
}
}
}
block_167:
{
uint8_t x_165; 
x_165 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_165 == 0)
{
lean_dec_ref(x_157);
x_134 = x_163;
x_135 = x_161;
x_136 = x_158;
x_137 = x_159;
x_138 = x_160;
x_139 = x_162;
x_140 = lean_box(0);
x_141 = x_109;
goto block_156;
}
else
{
uint8_t x_166; 
x_166 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_157);
x_134 = x_163;
x_135 = x_161;
x_136 = x_158;
x_137 = x_159;
x_138 = x_160;
x_139 = x_162;
x_140 = lean_box(0);
x_141 = x_166;
goto block_156;
}
}
block_178:
{
if (x_176 == 0)
{
lean_dec_ref(x_168);
x_158 = x_170;
x_159 = x_172;
x_160 = x_174;
x_161 = x_171;
x_162 = x_169;
x_163 = x_175;
x_164 = lean_box(0);
goto block_167;
}
else
{
lean_object* x_177; 
lean_dec(x_175);
lean_dec_ref(x_174);
lean_dec(x_171);
lean_dec_ref(x_169);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_168);
return x_177;
}
}
block_189:
{
uint8_t x_187; 
x_187 = l_Lean_Exception_isInterrupt(x_185);
if (x_187 == 0)
{
uint8_t x_188; 
lean_inc_ref(x_185);
x_188 = l_Lean_Exception_isRuntime(x_185);
x_168 = x_185;
x_169 = x_179;
x_170 = x_180;
x_171 = x_181;
x_172 = x_182;
x_173 = lean_box(0);
x_174 = x_183;
x_175 = x_184;
x_176 = x_188;
goto block_178;
}
else
{
x_168 = x_185;
x_169 = x_179;
x_170 = x_180;
x_171 = x_181;
x_172 = x_182;
x_173 = lean_box(0);
x_174 = x_183;
x_175 = x_184;
x_176 = x_187;
goto block_178;
}
}
block_281:
{
lean_object* x_197; 
lean_inc(x_196);
lean_inc_ref(x_190);
lean_inc(x_192);
lean_inc_ref(x_195);
lean_inc_ref(x_157);
x_197 = l_Lean_Meta_mkDecide(x_157, x_195, x_192, x_190, x_196);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; lean_object* x_218; uint8_t x_219; uint8_t x_279; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec_ref(x_197);
x_199 = l_Lean_Meta_Context_config(x_195);
x_200 = lean_ctor_get_uint8(x_199, 0);
x_201 = lean_ctor_get_uint8(x_199, 1);
x_202 = lean_ctor_get_uint8(x_199, 2);
x_203 = lean_ctor_get_uint8(x_199, 3);
x_204 = lean_ctor_get_uint8(x_199, 4);
x_205 = lean_ctor_get_uint8(x_199, 5);
x_206 = lean_ctor_get_uint8(x_199, 6);
x_207 = lean_ctor_get_uint8(x_199, 7);
x_208 = lean_ctor_get_uint8(x_199, 8);
x_209 = lean_ctor_get_uint8(x_199, 10);
x_210 = lean_ctor_get_uint8(x_199, 11);
x_211 = lean_ctor_get_uint8(x_199, 12);
x_212 = lean_ctor_get_uint8(x_199, 13);
x_213 = lean_ctor_get_uint8(x_199, 14);
x_214 = lean_ctor_get_uint8(x_199, 15);
x_215 = lean_ctor_get_uint8(x_199, 16);
x_216 = lean_ctor_get_uint8(x_199, 17);
x_217 = lean_ctor_get_uint8(x_199, 18);
x_279 = !lean_is_exclusive(x_199);
if (x_279 == 0)
{
x_218 = x_199;
x_219 = x_279;
goto block_278;
}
else
{
lean_dec(x_199);
x_218 = lean_box(0);
x_219 = x_279;
goto block_278;
}
block_278:
{
uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; lean_object* x_231; 
x_220 = lean_ctor_get_uint8(x_195, sizeof(void*)*7);
x_221 = lean_ctor_get(x_195, 1);
x_222 = lean_ctor_get(x_195, 2);
x_223 = lean_ctor_get(x_195, 3);
x_224 = lean_ctor_get(x_195, 4);
x_225 = lean_ctor_get(x_195, 5);
x_226 = lean_ctor_get(x_195, 6);
x_227 = lean_ctor_get_uint8(x_195, sizeof(void*)*7 + 1);
x_228 = lean_ctor_get_uint8(x_195, sizeof(void*)*7 + 2);
x_229 = lean_ctor_get_uint8(x_195, sizeof(void*)*7 + 3);
x_230 = 1;
if (x_219 == 0)
{
x_231 = x_218;
goto block_276;
}
else
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_277, 0, x_200);
lean_ctor_set_uint8(x_277, 1, x_201);
lean_ctor_set_uint8(x_277, 2, x_202);
lean_ctor_set_uint8(x_277, 3, x_203);
lean_ctor_set_uint8(x_277, 4, x_204);
lean_ctor_set_uint8(x_277, 5, x_205);
lean_ctor_set_uint8(x_277, 6, x_206);
lean_ctor_set_uint8(x_277, 7, x_207);
lean_ctor_set_uint8(x_277, 8, x_208);
lean_ctor_set_uint8(x_277, 10, x_209);
lean_ctor_set_uint8(x_277, 11, x_210);
lean_ctor_set_uint8(x_277, 12, x_211);
lean_ctor_set_uint8(x_277, 13, x_212);
lean_ctor_set_uint8(x_277, 14, x_213);
lean_ctor_set_uint8(x_277, 15, x_214);
lean_ctor_set_uint8(x_277, 16, x_215);
lean_ctor_set_uint8(x_277, 17, x_216);
lean_ctor_set_uint8(x_277, 18, x_217);
x_231 = x_277;
goto block_276;
}
block_276:
{
uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_ctor_set_uint8(x_231, 9, x_230);
x_232 = l_Lean_Meta_Context_configKey(x_195);
x_233 = 2;
x_234 = lean_uint64_shift_right(x_232, x_233);
x_235 = lean_uint64_shift_left(x_234, x_233);
x_236 = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
x_237 = lean_uint64_lor(x_235, x_236);
x_238 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_238, 0, x_231);
lean_ctor_set_uint64(x_238, sizeof(void*)*1, x_237);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc_ref(x_223);
lean_inc_ref(x_222);
lean_inc(x_221);
x_239 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_221);
lean_ctor_set(x_239, 2, x_222);
lean_ctor_set(x_239, 3, x_223);
lean_ctor_set(x_239, 4, x_224);
lean_ctor_set(x_239, 5, x_225);
lean_ctor_set(x_239, 6, x_226);
lean_ctor_set_uint8(x_239, sizeof(void*)*7, x_220);
lean_ctor_set_uint8(x_239, sizeof(void*)*7 + 1, x_227);
lean_ctor_set_uint8(x_239, sizeof(void*)*7 + 2, x_228);
lean_ctor_set_uint8(x_239, sizeof(void*)*7 + 3, x_229);
lean_inc(x_196);
lean_inc_ref(x_190);
lean_inc(x_192);
lean_inc(x_198);
x_240 = lean_whnf(x_198, x_239, x_192, x_190, x_196);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
lean_dec_ref(x_240);
x_242 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
x_243 = l_Lean_Expr_isConstOf(x_241, x_242);
lean_dec(x_241);
if (x_243 == 0)
{
lean_dec(x_198);
x_158 = x_191;
x_159 = x_193;
x_160 = x_195;
x_161 = x_192;
x_162 = x_190;
x_163 = x_196;
x_164 = lean_box(0);
goto block_167;
}
else
{
lean_object* x_244; 
lean_inc(x_196);
lean_inc_ref(x_190);
lean_inc(x_192);
lean_inc_ref(x_195);
lean_inc(x_198);
x_244 = l_Lean_Meta_mkEqRefl(x_198, x_195, x_192, x_190, x_196);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec_ref(x_244);
lean_inc(x_2);
x_246 = l_Lean_MVarId_getType(x_2, x_195, x_192, x_190, x_196);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_248 = l_Lean_Expr_getAppNumArgs(x_198);
x_249 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
x_250 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(x_248);
x_251 = lean_mk_array(x_248, x_250);
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_nat_sub(x_248, x_252);
lean_dec(x_248);
x_254 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_198, x_251, x_253);
x_255 = lean_array_push(x_254, x_245);
x_256 = l_Lean_mkAppN(x_249, x_255);
lean_dec_ref(x_255);
lean_inc(x_34);
x_257 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_196);
lean_inc_ref(x_190);
lean_inc(x_192);
lean_inc_ref(x_195);
x_258 = l_Lean_Meta_mkAbsurd(x_247, x_257, x_256, x_195, x_192, x_190, x_196);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
lean_inc(x_2);
x_260 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_259, x_192);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; uint8_t x_262; uint8_t x_269; 
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec(x_192);
lean_dec_ref(x_190);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_269 = !lean_is_exclusive(x_260);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_260, 0);
lean_dec(x_270);
x_261 = x_260;
x_262 = x_269;
goto block_268;
}
else
{
lean_dec(x_260);
x_261 = lean_box(0);
x_262 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_box(x_12);
if (x_262 == 0)
{
lean_ctor_set_tag(x_261, 1);
lean_ctor_set(x_261, 0, x_263);
x_264 = x_261;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_263);
x_264 = x_267;
goto block_266;
}
block_266:
{
lean_object* x_265; 
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_37);
x_17 = x_265;
x_18 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_260, 0);
lean_inc(x_271);
lean_dec_ref(x_260);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_271;
x_186 = lean_box(0);
goto block_189;
}
}
else
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_258, 0);
lean_inc(x_272);
lean_dec_ref(x_258);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_272;
x_186 = lean_box(0);
goto block_189;
}
}
else
{
lean_object* x_273; 
lean_dec(x_245);
lean_dec(x_198);
x_273 = lean_ctor_get(x_246, 0);
lean_inc(x_273);
lean_dec_ref(x_246);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_273;
x_186 = lean_box(0);
goto block_189;
}
}
else
{
lean_object* x_274; 
lean_dec(x_198);
x_274 = lean_ctor_get(x_244, 0);
lean_inc(x_274);
lean_dec_ref(x_244);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_274;
x_186 = lean_box(0);
goto block_189;
}
}
}
else
{
lean_object* x_275; 
lean_dec(x_198);
x_275 = lean_ctor_get(x_240, 0);
lean_inc(x_275);
lean_dec_ref(x_240);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_275;
x_186 = lean_box(0);
goto block_189;
}
}
}
}
else
{
lean_object* x_280; 
x_280 = lean_ctor_get(x_197, 0);
lean_inc(x_280);
lean_dec_ref(x_197);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_280;
x_186 = lean_box(0);
goto block_189;
}
}
block_290:
{
if (x_289 == 0)
{
x_158 = x_283;
x_159 = x_285;
x_160 = x_287;
x_161 = x_284;
x_162 = x_282;
x_163 = x_288;
x_164 = lean_box(0);
goto block_167;
}
else
{
x_190 = x_282;
x_191 = x_283;
x_192 = x_284;
x_193 = x_285;
x_194 = lean_box(0);
x_195 = x_287;
x_196 = x_288;
goto block_281;
}
}
block_301:
{
if (x_299 == 0)
{
lean_dec_ref(x_292);
x_282 = x_291;
x_283 = x_293;
x_284 = x_294;
x_285 = x_296;
x_286 = lean_box(0);
x_287 = x_297;
x_288 = x_298;
x_289 = x_109;
goto block_290;
}
else
{
uint8_t x_300; 
x_300 = l_Lean_Expr_hasFVar(x_292);
lean_dec_ref(x_292);
if (x_300 == 0)
{
x_190 = x_291;
x_191 = x_293;
x_192 = x_294;
x_193 = x_296;
x_194 = lean_box(0);
x_195 = x_297;
x_196 = x_298;
goto block_281;
}
else
{
x_282 = x_291;
x_283 = x_293;
x_284 = x_294;
x_285 = x_296;
x_286 = lean_box(0);
x_287 = x_297;
x_288 = x_298;
x_289 = x_109;
goto block_290;
}
}
}
block_321:
{
lean_object* x_310; 
lean_inc_ref(x_157);
x_310 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_157, x_304);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; uint8_t x_312; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
lean_dec_ref(x_310);
x_312 = l_Lean_Expr_hasMVar(x_311);
if (x_312 == 0)
{
x_291 = x_302;
x_292 = x_311;
x_293 = x_303;
x_294 = x_304;
x_295 = lean_box(0);
x_296 = x_305;
x_297 = x_306;
x_298 = x_308;
x_299 = x_309;
goto block_301;
}
else
{
x_291 = x_302;
x_292 = x_311;
x_293 = x_303;
x_294 = x_304;
x_295 = lean_box(0);
x_296 = x_305;
x_297 = x_306;
x_298 = x_308;
x_299 = x_109;
goto block_301;
}
}
else
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; uint8_t x_320; 
lean_dec(x_308);
lean_dec_ref(x_306);
lean_dec(x_304);
lean_dec_ref(x_302);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_313 = lean_ctor_get(x_310, 0);
x_320 = !lean_is_exclusive(x_310);
if (x_320 == 0)
{
x_314 = x_310;
x_315 = x_320;
goto block_319;
}
else
{
lean_inc(x_313);
lean_dec(x_310);
x_314 = lean_box(0);
x_315 = x_320;
goto block_319;
}
block_319:
{
lean_object* x_316; 
if (x_315 == 0)
{
x_316 = x_314;
goto block_317;
}
else
{
lean_object* x_318; 
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_313);
x_316 = x_318;
goto block_317;
}
block_317:
{
return x_316;
}
}
}
}
block_330:
{
if (x_329 == 0)
{
x_158 = x_323;
x_159 = x_325;
x_160 = x_327;
x_161 = x_324;
x_162 = x_322;
x_163 = x_328;
x_164 = lean_box(0);
goto block_167;
}
else
{
x_302 = x_322;
x_303 = x_323;
x_304 = x_324;
x_305 = x_325;
x_306 = x_327;
x_307 = lean_box(0);
x_308 = x_328;
x_309 = x_329;
goto block_321;
}
}
block_340:
{
uint8_t x_338; 
x_338 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_338 == 0)
{
x_322 = x_335;
x_323 = x_332;
x_324 = x_334;
x_325 = x_331;
x_326 = lean_box(0);
x_327 = x_333;
x_328 = x_336;
x_329 = x_109;
goto block_330;
}
else
{
uint8_t x_339; 
x_339 = l_Lean_Expr_hasFVar(x_157);
if (x_339 == 0)
{
x_302 = x_335;
x_303 = x_332;
x_304 = x_334;
x_305 = x_331;
x_306 = x_333;
x_307 = lean_box(0);
x_308 = x_336;
x_309 = x_338;
goto block_321;
}
else
{
x_322 = x_335;
x_323 = x_332;
x_324 = x_334;
x_325 = x_331;
x_326 = lean_box(0);
x_327 = x_333;
x_328 = x_336;
x_329 = x_109;
goto block_330;
}
}
}
block_403:
{
lean_object* x_349; 
lean_inc(x_345);
lean_inc_ref(x_341);
lean_inc(x_348);
lean_inc_ref(x_343);
x_349 = l_Lean_Meta_isExprDefEq(x_346, x_347, x_343, x_348, x_341, x_345);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; uint8_t x_351; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
lean_dec_ref(x_349);
x_351 = lean_unbox(x_350);
lean_dec(x_350);
if (x_351 == 0)
{
x_331 = x_344;
x_332 = x_12;
x_333 = x_343;
x_334 = x_348;
x_335 = x_341;
x_336 = x_345;
x_337 = lean_box(0);
goto block_340;
}
else
{
lean_object* x_352; 
lean_dec_ref(x_157);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_352 = l_Lean_MVarId_getType(x_2, x_343, x_348, x_341, x_345);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec_ref(x_352);
x_354 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_345);
lean_inc_ref(x_341);
lean_inc(x_348);
lean_inc_ref(x_343);
x_355 = l_Lean_Meta_mkEqOfHEq(x_354, x_12, x_343, x_348, x_341, x_345);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
lean_dec_ref(x_355);
lean_inc(x_348);
x_357 = l_Lean_Meta_mkNoConfusion(x_353, x_356, x_343, x_348, x_341, x_345);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
lean_dec_ref(x_357);
x_359 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_358, x_348);
lean_dec(x_348);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec_ref(x_359);
x_360 = lean_box(x_12);
x_361 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_361, 0, x_360);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_37);
x_17 = x_362;
x_18 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_363; lean_object* x_364; uint8_t x_365; uint8_t x_370; 
lean_del_object(x_15);
lean_dec(x_14);
x_363 = lean_ctor_get(x_359, 0);
x_370 = !lean_is_exclusive(x_359);
if (x_370 == 0)
{
x_364 = x_359;
x_365 = x_370;
goto block_369;
}
else
{
lean_inc(x_363);
lean_dec(x_359);
x_364 = lean_box(0);
x_365 = x_370;
goto block_369;
}
block_369:
{
lean_object* x_366; 
if (x_365 == 0)
{
x_366 = x_364;
goto block_367;
}
else
{
lean_object* x_368; 
x_368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_368, 0, x_363);
x_366 = x_368;
goto block_367;
}
block_367:
{
return x_366;
}
}
}
}
else
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; uint8_t x_378; 
lean_dec(x_348);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_371 = lean_ctor_get(x_357, 0);
x_378 = !lean_is_exclusive(x_357);
if (x_378 == 0)
{
x_372 = x_357;
x_373 = x_378;
goto block_377;
}
else
{
lean_inc(x_371);
lean_dec(x_357);
x_372 = lean_box(0);
x_373 = x_378;
goto block_377;
}
block_377:
{
lean_object* x_374; 
if (x_373 == 0)
{
x_374 = x_372;
goto block_375;
}
else
{
lean_object* x_376; 
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_371);
x_374 = x_376;
goto block_375;
}
block_375:
{
return x_374;
}
}
}
}
else
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; uint8_t x_386; 
lean_dec(x_353);
lean_dec(x_348);
lean_dec(x_345);
lean_dec_ref(x_343);
lean_dec_ref(x_341);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_379 = lean_ctor_get(x_355, 0);
x_386 = !lean_is_exclusive(x_355);
if (x_386 == 0)
{
x_380 = x_355;
x_381 = x_386;
goto block_385;
}
else
{
lean_inc(x_379);
lean_dec(x_355);
x_380 = lean_box(0);
x_381 = x_386;
goto block_385;
}
block_385:
{
lean_object* x_382; 
if (x_381 == 0)
{
x_382 = x_380;
goto block_383;
}
else
{
lean_object* x_384; 
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_379);
x_382 = x_384;
goto block_383;
}
block_383:
{
return x_382;
}
}
}
}
else
{
lean_object* x_387; lean_object* x_388; uint8_t x_389; uint8_t x_394; 
lean_dec(x_348);
lean_dec(x_345);
lean_dec_ref(x_343);
lean_dec_ref(x_341);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_387 = lean_ctor_get(x_352, 0);
x_394 = !lean_is_exclusive(x_352);
if (x_394 == 0)
{
x_388 = x_352;
x_389 = x_394;
goto block_393;
}
else
{
lean_inc(x_387);
lean_dec(x_352);
x_388 = lean_box(0);
x_389 = x_394;
goto block_393;
}
block_393:
{
lean_object* x_390; 
if (x_389 == 0)
{
x_390 = x_388;
goto block_391;
}
else
{
lean_object* x_392; 
x_392 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_392, 0, x_387);
x_390 = x_392;
goto block_391;
}
block_391:
{
return x_390;
}
}
}
}
}
else
{
lean_object* x_395; lean_object* x_396; uint8_t x_397; uint8_t x_402; 
lean_dec(x_348);
lean_dec(x_345);
lean_dec_ref(x_343);
lean_dec_ref(x_341);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_395 = lean_ctor_get(x_349, 0);
x_402 = !lean_is_exclusive(x_349);
if (x_402 == 0)
{
x_396 = x_349;
x_397 = x_402;
goto block_401;
}
else
{
lean_inc(x_395);
lean_dec(x_349);
x_396 = lean_box(0);
x_397 = x_402;
goto block_401;
}
block_401:
{
lean_object* x_398; 
if (x_397 == 0)
{
x_398 = x_396;
goto block_399;
}
else
{
lean_object* x_400; 
x_400 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_400, 0, x_395);
x_398 = x_400;
goto block_399;
}
block_399:
{
return x_398;
}
}
}
}
block_454:
{
lean_object* x_410; 
lean_inc(x_408);
lean_inc_ref(x_407);
lean_inc(x_406);
lean_inc_ref(x_405);
lean_inc_ref(x_157);
x_410 = l_Lean_Meta_matchHEq_x3f(x_157, x_405, x_406, x_407, x_408);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
lean_dec_ref(x_410);
if (lean_obj_tag(x_411) == 1)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
lean_dec_ref(x_411);
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_412, 0);
lean_inc(x_415);
lean_dec(x_412);
x_416 = lean_ctor_get(x_413, 0);
lean_inc(x_416);
lean_dec(x_413);
x_417 = lean_ctor_get(x_414, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_414, 1);
lean_inc(x_418);
lean_dec(x_414);
lean_inc(x_408);
lean_inc_ref(x_407);
lean_inc(x_406);
lean_inc_ref(x_405);
x_419 = l_Lean_Meta_matchConstructorApp_x3f(x_416, x_405, x_406, x_407, x_408);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
lean_dec_ref(x_419);
if (lean_obj_tag(x_420) == 1)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
lean_dec_ref(x_420);
lean_inc(x_408);
lean_inc_ref(x_407);
lean_inc(x_406);
lean_inc_ref(x_405);
x_422 = l_Lean_Meta_matchConstructorApp_x3f(x_418, x_405, x_406, x_407, x_408);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
lean_dec_ref(x_422);
if (lean_obj_tag(x_423) == 1)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_424 = lean_ctor_get(x_421, 0);
lean_inc_ref(x_424);
lean_dec(x_421);
x_425 = lean_ctor_get(x_423, 0);
lean_inc(x_425);
lean_dec_ref(x_423);
x_426 = lean_ctor_get(x_425, 0);
lean_inc_ref(x_426);
lean_dec(x_425);
x_427 = lean_ctor_get(x_424, 0);
lean_inc(x_427);
lean_dec_ref(x_424);
x_428 = lean_ctor_get(x_426, 0);
lean_inc(x_428);
lean_dec_ref(x_426);
x_429 = lean_name_eq(x_427, x_428);
lean_dec(x_428);
lean_dec(x_427);
if (x_429 == 0)
{
x_341 = x_407;
x_342 = lean_box(0);
x_343 = x_405;
x_344 = x_404;
x_345 = x_408;
x_346 = x_415;
x_347 = x_417;
x_348 = x_406;
goto block_403;
}
else
{
if (x_109 == 0)
{
lean_dec(x_417);
lean_dec(x_415);
x_331 = x_404;
x_332 = x_12;
x_333 = x_405;
x_334 = x_406;
x_335 = x_407;
x_336 = x_408;
x_337 = lean_box(0);
goto block_340;
}
else
{
x_341 = x_407;
x_342 = lean_box(0);
x_343 = x_405;
x_344 = x_404;
x_345 = x_408;
x_346 = x_415;
x_347 = x_417;
x_348 = x_406;
goto block_403;
}
}
}
else
{
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_417);
lean_dec(x_415);
x_331 = x_404;
x_332 = x_12;
x_333 = x_405;
x_334 = x_406;
x_335 = x_407;
x_336 = x_408;
x_337 = lean_box(0);
goto block_340;
}
}
else
{
lean_object* x_430; lean_object* x_431; uint8_t x_432; uint8_t x_437; 
lean_dec(x_421);
lean_dec(x_417);
lean_dec(x_415);
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
lean_dec_ref(x_405);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_430 = lean_ctor_get(x_422, 0);
x_437 = !lean_is_exclusive(x_422);
if (x_437 == 0)
{
x_431 = x_422;
x_432 = x_437;
goto block_436;
}
else
{
lean_inc(x_430);
lean_dec(x_422);
x_431 = lean_box(0);
x_432 = x_437;
goto block_436;
}
block_436:
{
lean_object* x_433; 
if (x_432 == 0)
{
x_433 = x_431;
goto block_434;
}
else
{
lean_object* x_435; 
x_435 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_435, 0, x_430);
x_433 = x_435;
goto block_434;
}
block_434:
{
return x_433;
}
}
}
}
else
{
lean_dec(x_420);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_415);
x_331 = x_404;
x_332 = x_12;
x_333 = x_405;
x_334 = x_406;
x_335 = x_407;
x_336 = x_408;
x_337 = lean_box(0);
goto block_340;
}
}
else
{
lean_object* x_438; lean_object* x_439; uint8_t x_440; uint8_t x_445; 
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_415);
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
lean_dec_ref(x_405);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_438 = lean_ctor_get(x_419, 0);
x_445 = !lean_is_exclusive(x_419);
if (x_445 == 0)
{
x_439 = x_419;
x_440 = x_445;
goto block_444;
}
else
{
lean_inc(x_438);
lean_dec(x_419);
x_439 = lean_box(0);
x_440 = x_445;
goto block_444;
}
block_444:
{
lean_object* x_441; 
if (x_440 == 0)
{
x_441 = x_439;
goto block_442;
}
else
{
lean_object* x_443; 
x_443 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_443, 0, x_438);
x_441 = x_443;
goto block_442;
}
block_442:
{
return x_441;
}
}
}
}
else
{
lean_dec(x_411);
x_331 = x_404;
x_332 = x_109;
x_333 = x_405;
x_334 = x_406;
x_335 = x_407;
x_336 = x_408;
x_337 = lean_box(0);
goto block_340;
}
}
else
{
lean_object* x_446; lean_object* x_447; uint8_t x_448; uint8_t x_453; 
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
lean_dec_ref(x_405);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_446 = lean_ctor_get(x_410, 0);
x_453 = !lean_is_exclusive(x_410);
if (x_453 == 0)
{
x_447 = x_410;
x_448 = x_453;
goto block_452;
}
else
{
lean_inc(x_446);
lean_dec(x_410);
x_447 = lean_box(0);
x_448 = x_453;
goto block_452;
}
block_452:
{
lean_object* x_449; 
if (x_448 == 0)
{
x_449 = x_447;
goto block_450;
}
else
{
lean_object* x_451; 
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_446);
x_449 = x_451;
goto block_450;
}
block_450:
{
return x_449;
}
}
}
}
block_501:
{
lean_object* x_460; 
lean_inc(x_458);
lean_inc_ref(x_457);
lean_inc(x_456);
lean_inc_ref(x_455);
lean_inc_ref(x_157);
x_460 = l_Lean_Meta_matchEq_x3f(x_157, x_455, x_456, x_457, x_458);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
lean_dec_ref(x_460);
if (lean_obj_tag(x_461) == 1)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
lean_dec_ref(x_461);
x_463 = lean_ctor_get(x_462, 1);
lean_inc(x_463);
lean_dec(x_462);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
lean_inc(x_458);
lean_inc_ref(x_457);
lean_inc(x_456);
lean_inc_ref(x_455);
x_466 = l_Lean_Meta_matchConstructorApp_x3f(x_464, x_455, x_456, x_457, x_458);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
lean_dec_ref(x_466);
if (lean_obj_tag(x_467) == 1)
{
lean_object* x_468; lean_object* x_469; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
lean_dec_ref(x_467);
lean_inc(x_458);
lean_inc_ref(x_457);
lean_inc(x_456);
lean_inc_ref(x_455);
x_469 = l_Lean_Meta_matchConstructorApp_x3f(x_465, x_455, x_456, x_457, x_458);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
lean_dec_ref(x_469);
if (lean_obj_tag(x_470) == 1)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_471 = lean_ctor_get(x_468, 0);
lean_inc_ref(x_471);
lean_dec(x_468);
x_472 = lean_ctor_get(x_470, 0);
lean_inc(x_472);
lean_dec_ref(x_470);
x_473 = lean_ctor_get(x_472, 0);
lean_inc_ref(x_473);
lean_dec(x_472);
x_474 = lean_ctor_get(x_471, 0);
lean_inc(x_474);
lean_dec_ref(x_471);
x_475 = lean_ctor_get(x_473, 0);
lean_inc(x_475);
lean_dec_ref(x_473);
x_476 = lean_name_eq(x_474, x_475);
lean_dec(x_475);
lean_dec(x_474);
if (x_476 == 0)
{
lean_dec_ref(x_157);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_38 = lean_box(0);
x_39 = x_458;
x_40 = x_456;
x_41 = x_455;
x_42 = x_457;
goto block_78;
}
else
{
if (x_109 == 0)
{
lean_del_object(x_35);
x_404 = x_12;
x_405 = x_455;
x_406 = x_456;
x_407 = x_457;
x_408 = x_458;
x_409 = lean_box(0);
goto block_454;
}
else
{
lean_dec_ref(x_157);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_38 = lean_box(0);
x_39 = x_458;
x_40 = x_456;
x_41 = x_455;
x_42 = x_457;
goto block_78;
}
}
}
else
{
lean_dec(x_470);
lean_dec(x_468);
lean_del_object(x_35);
x_404 = x_12;
x_405 = x_455;
x_406 = x_456;
x_407 = x_457;
x_408 = x_458;
x_409 = lean_box(0);
goto block_454;
}
}
else
{
lean_object* x_477; lean_object* x_478; uint8_t x_479; uint8_t x_484; 
lean_dec(x_468);
lean_dec(x_458);
lean_dec_ref(x_457);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_477 = lean_ctor_get(x_469, 0);
x_484 = !lean_is_exclusive(x_469);
if (x_484 == 0)
{
x_478 = x_469;
x_479 = x_484;
goto block_483;
}
else
{
lean_inc(x_477);
lean_dec(x_469);
x_478 = lean_box(0);
x_479 = x_484;
goto block_483;
}
block_483:
{
lean_object* x_480; 
if (x_479 == 0)
{
x_480 = x_478;
goto block_481;
}
else
{
lean_object* x_482; 
x_482 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_482, 0, x_477);
x_480 = x_482;
goto block_481;
}
block_481:
{
return x_480;
}
}
}
}
else
{
lean_dec(x_467);
lean_dec(x_465);
lean_del_object(x_35);
x_404 = x_12;
x_405 = x_455;
x_406 = x_456;
x_407 = x_457;
x_408 = x_458;
x_409 = lean_box(0);
goto block_454;
}
}
else
{
lean_object* x_485; lean_object* x_486; uint8_t x_487; uint8_t x_492; 
lean_dec(x_465);
lean_dec(x_458);
lean_dec_ref(x_457);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_485 = lean_ctor_get(x_466, 0);
x_492 = !lean_is_exclusive(x_466);
if (x_492 == 0)
{
x_486 = x_466;
x_487 = x_492;
goto block_491;
}
else
{
lean_inc(x_485);
lean_dec(x_466);
x_486 = lean_box(0);
x_487 = x_492;
goto block_491;
}
block_491:
{
lean_object* x_488; 
if (x_487 == 0)
{
x_488 = x_486;
goto block_489;
}
else
{
lean_object* x_490; 
x_490 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_490, 0, x_485);
x_488 = x_490;
goto block_489;
}
block_489:
{
return x_488;
}
}
}
}
else
{
lean_dec(x_461);
lean_del_object(x_35);
x_404 = x_109;
x_405 = x_455;
x_406 = x_456;
x_407 = x_457;
x_408 = x_458;
x_409 = lean_box(0);
goto block_454;
}
}
else
{
lean_object* x_493; lean_object* x_494; uint8_t x_495; uint8_t x_500; 
lean_dec(x_458);
lean_dec_ref(x_457);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_493 = lean_ctor_get(x_460, 0);
x_500 = !lean_is_exclusive(x_460);
if (x_500 == 0)
{
x_494 = x_460;
x_495 = x_500;
goto block_499;
}
else
{
lean_inc(x_493);
lean_dec(x_460);
x_494 = lean_box(0);
x_495 = x_500;
goto block_499;
}
block_499:
{
lean_object* x_496; 
if (x_495 == 0)
{
x_496 = x_494;
goto block_497;
}
else
{
lean_object* x_498; 
x_498 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_498, 0, x_493);
x_496 = x_498;
goto block_497;
}
block_497:
{
return x_496;
}
}
}
}
block_637:
{
lean_object* x_507; 
lean_inc(x_505);
lean_inc_ref(x_504);
lean_inc(x_503);
lean_inc_ref(x_502);
lean_inc_ref(x_157);
x_507 = l_refutableHasNotBit_x3f(x_157, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
lean_dec_ref(x_507);
if (lean_obj_tag(x_508) == 1)
{
lean_object* x_509; lean_object* x_510; uint8_t x_511; uint8_t x_548; 
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_509 = lean_ctor_get(x_508, 0);
x_548 = !lean_is_exclusive(x_508);
if (x_548 == 0)
{
x_510 = x_508;
x_511 = x_548;
goto block_547;
}
else
{
lean_inc(x_509);
lean_dec(x_508);
x_510 = lean_box(0);
x_511 = x_548;
goto block_547;
}
block_547:
{
lean_object* x_512; 
lean_inc(x_2);
x_512 = l_Lean_MVarId_getType(x_2, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
lean_dec_ref(x_512);
x_514 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_503);
x_515 = l_Lean_Meta_mkAbsurd(x_513, x_509, x_514, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
lean_dec_ref(x_515);
x_517 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_516, x_503);
lean_dec(x_503);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; 
lean_dec_ref(x_517);
x_518 = lean_box(x_12);
if (x_511 == 0)
{
lean_ctor_set(x_510, 0, x_518);
x_519 = x_510;
goto block_521;
}
else
{
lean_object* x_522; 
x_522 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_522, 0, x_518);
x_519 = x_522;
goto block_521;
}
block_521:
{
lean_object* x_520; 
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_37);
x_17 = x_520;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_523; lean_object* x_524; uint8_t x_525; uint8_t x_530; 
lean_del_object(x_510);
lean_del_object(x_15);
lean_dec(x_14);
x_523 = lean_ctor_get(x_517, 0);
x_530 = !lean_is_exclusive(x_517);
if (x_530 == 0)
{
x_524 = x_517;
x_525 = x_530;
goto block_529;
}
else
{
lean_inc(x_523);
lean_dec(x_517);
x_524 = lean_box(0);
x_525 = x_530;
goto block_529;
}
block_529:
{
lean_object* x_526; 
if (x_525 == 0)
{
x_526 = x_524;
goto block_527;
}
else
{
lean_object* x_528; 
x_528 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_528, 0, x_523);
x_526 = x_528;
goto block_527;
}
block_527:
{
return x_526;
}
}
}
}
else
{
lean_object* x_531; lean_object* x_532; uint8_t x_533; uint8_t x_538; 
lean_del_object(x_510);
lean_dec(x_503);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_531 = lean_ctor_get(x_515, 0);
x_538 = !lean_is_exclusive(x_515);
if (x_538 == 0)
{
x_532 = x_515;
x_533 = x_538;
goto block_537;
}
else
{
lean_inc(x_531);
lean_dec(x_515);
x_532 = lean_box(0);
x_533 = x_538;
goto block_537;
}
block_537:
{
lean_object* x_534; 
if (x_533 == 0)
{
x_534 = x_532;
goto block_535;
}
else
{
lean_object* x_536; 
x_536 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_536, 0, x_531);
x_534 = x_536;
goto block_535;
}
block_535:
{
return x_534;
}
}
}
}
else
{
lean_object* x_539; lean_object* x_540; uint8_t x_541; uint8_t x_546; 
lean_del_object(x_510);
lean_dec(x_509);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_539 = lean_ctor_get(x_512, 0);
x_546 = !lean_is_exclusive(x_512);
if (x_546 == 0)
{
x_540 = x_512;
x_541 = x_546;
goto block_545;
}
else
{
lean_inc(x_539);
lean_dec(x_512);
x_540 = lean_box(0);
x_541 = x_546;
goto block_545;
}
block_545:
{
lean_object* x_542; 
if (x_541 == 0)
{
x_542 = x_540;
goto block_543;
}
else
{
lean_object* x_544; 
x_544 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_544, 0, x_539);
x_542 = x_544;
goto block_543;
}
block_543:
{
return x_542;
}
}
}
}
}
else
{
lean_object* x_549; 
lean_dec(x_508);
lean_inc(x_505);
lean_inc_ref(x_504);
lean_inc(x_503);
lean_inc_ref(x_502);
lean_inc_ref(x_157);
x_549 = l_Lean_Meta_matchNe_x3f(x_157, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
lean_dec_ref(x_549);
if (lean_obj_tag(x_550) == 1)
{
lean_object* x_551; lean_object* x_552; uint8_t x_553; uint8_t x_620; 
x_551 = lean_ctor_get(x_550, 0);
x_620 = !lean_is_exclusive(x_550);
if (x_620 == 0)
{
x_552 = x_550;
x_553 = x_620;
goto block_619;
}
else
{
lean_inc(x_551);
lean_dec(x_550);
x_552 = lean_box(0);
x_553 = x_620;
goto block_619;
}
block_619:
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint8_t x_558; uint8_t x_618; 
x_554 = lean_ctor_get(x_551, 1);
lean_inc(x_554);
lean_dec(x_551);
x_555 = lean_ctor_get(x_554, 0);
x_556 = lean_ctor_get(x_554, 1);
x_618 = !lean_is_exclusive(x_554);
if (x_618 == 0)
{
x_557 = x_554;
x_558 = x_618;
goto block_617;
}
else
{
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_554);
x_557 = lean_box(0);
x_558 = x_618;
goto block_617;
}
block_617:
{
lean_object* x_559; 
lean_inc(x_505);
lean_inc_ref(x_504);
lean_inc(x_503);
lean_inc_ref(x_502);
lean_inc(x_555);
x_559 = l_Lean_Meta_isExprDefEq(x_555, x_556, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; uint8_t x_561; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
lean_dec_ref(x_559);
x_561 = lean_unbox(x_560);
lean_dec(x_560);
if (x_561 == 0)
{
lean_del_object(x_557);
lean_dec(x_555);
lean_del_object(x_552);
x_455 = x_502;
x_456 = x_503;
x_457 = x_504;
x_458 = x_505;
x_459 = lean_box(0);
goto block_501;
}
else
{
lean_object* x_562; 
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_562 = l_Lean_MVarId_getType(x_2, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
lean_dec_ref(x_562);
lean_inc(x_505);
lean_inc_ref(x_504);
lean_inc(x_503);
lean_inc_ref(x_502);
x_564 = l_Lean_Meta_mkEqRefl(x_555, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
lean_dec_ref(x_564);
x_566 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_503);
x_567 = l_Lean_Meta_mkAbsurd(x_563, x_565, x_566, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
lean_dec_ref(x_567);
x_569 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_568, x_503);
lean_dec(x_503);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; 
lean_dec_ref(x_569);
x_570 = lean_box(x_12);
if (x_553 == 0)
{
lean_ctor_set(x_552, 0, x_570);
x_571 = x_552;
goto block_575;
}
else
{
lean_object* x_576; 
x_576 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_576, 0, x_570);
x_571 = x_576;
goto block_575;
}
block_575:
{
lean_object* x_572; 
if (x_558 == 0)
{
lean_ctor_set(x_557, 1, x_37);
lean_ctor_set(x_557, 0, x_571);
x_572 = x_557;
goto block_573;
}
else
{
lean_object* x_574; 
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_571);
lean_ctor_set(x_574, 1, x_37);
x_572 = x_574;
goto block_573;
}
block_573:
{
x_17 = x_572;
x_18 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_577; lean_object* x_578; uint8_t x_579; uint8_t x_584; 
lean_del_object(x_557);
lean_del_object(x_552);
lean_del_object(x_15);
lean_dec(x_14);
x_577 = lean_ctor_get(x_569, 0);
x_584 = !lean_is_exclusive(x_569);
if (x_584 == 0)
{
x_578 = x_569;
x_579 = x_584;
goto block_583;
}
else
{
lean_inc(x_577);
lean_dec(x_569);
x_578 = lean_box(0);
x_579 = x_584;
goto block_583;
}
block_583:
{
lean_object* x_580; 
if (x_579 == 0)
{
x_580 = x_578;
goto block_581;
}
else
{
lean_object* x_582; 
x_582 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_582, 0, x_577);
x_580 = x_582;
goto block_581;
}
block_581:
{
return x_580;
}
}
}
}
else
{
lean_object* x_585; lean_object* x_586; uint8_t x_587; uint8_t x_592; 
lean_del_object(x_557);
lean_del_object(x_552);
lean_dec(x_503);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_585 = lean_ctor_get(x_567, 0);
x_592 = !lean_is_exclusive(x_567);
if (x_592 == 0)
{
x_586 = x_567;
x_587 = x_592;
goto block_591;
}
else
{
lean_inc(x_585);
lean_dec(x_567);
x_586 = lean_box(0);
x_587 = x_592;
goto block_591;
}
block_591:
{
lean_object* x_588; 
if (x_587 == 0)
{
x_588 = x_586;
goto block_589;
}
else
{
lean_object* x_590; 
x_590 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_590, 0, x_585);
x_588 = x_590;
goto block_589;
}
block_589:
{
return x_588;
}
}
}
}
else
{
lean_object* x_593; lean_object* x_594; uint8_t x_595; uint8_t x_600; 
lean_dec(x_563);
lean_del_object(x_557);
lean_del_object(x_552);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_593 = lean_ctor_get(x_564, 0);
x_600 = !lean_is_exclusive(x_564);
if (x_600 == 0)
{
x_594 = x_564;
x_595 = x_600;
goto block_599;
}
else
{
lean_inc(x_593);
lean_dec(x_564);
x_594 = lean_box(0);
x_595 = x_600;
goto block_599;
}
block_599:
{
lean_object* x_596; 
if (x_595 == 0)
{
x_596 = x_594;
goto block_597;
}
else
{
lean_object* x_598; 
x_598 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_598, 0, x_593);
x_596 = x_598;
goto block_597;
}
block_597:
{
return x_596;
}
}
}
}
else
{
lean_object* x_601; lean_object* x_602; uint8_t x_603; uint8_t x_608; 
lean_del_object(x_557);
lean_dec(x_555);
lean_del_object(x_552);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_601 = lean_ctor_get(x_562, 0);
x_608 = !lean_is_exclusive(x_562);
if (x_608 == 0)
{
x_602 = x_562;
x_603 = x_608;
goto block_607;
}
else
{
lean_inc(x_601);
lean_dec(x_562);
x_602 = lean_box(0);
x_603 = x_608;
goto block_607;
}
block_607:
{
lean_object* x_604; 
if (x_603 == 0)
{
x_604 = x_602;
goto block_605;
}
else
{
lean_object* x_606; 
x_606 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_606, 0, x_601);
x_604 = x_606;
goto block_605;
}
block_605:
{
return x_604;
}
}
}
}
}
else
{
lean_object* x_609; lean_object* x_610; uint8_t x_611; uint8_t x_616; 
lean_del_object(x_557);
lean_dec(x_555);
lean_del_object(x_552);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_609 = lean_ctor_get(x_559, 0);
x_616 = !lean_is_exclusive(x_559);
if (x_616 == 0)
{
x_610 = x_559;
x_611 = x_616;
goto block_615;
}
else
{
lean_inc(x_609);
lean_dec(x_559);
x_610 = lean_box(0);
x_611 = x_616;
goto block_615;
}
block_615:
{
lean_object* x_612; 
if (x_611 == 0)
{
x_612 = x_610;
goto block_613;
}
else
{
lean_object* x_614; 
x_614 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_614, 0, x_609);
x_612 = x_614;
goto block_613;
}
block_613:
{
return x_612;
}
}
}
}
}
}
else
{
lean_dec(x_550);
x_455 = x_502;
x_456 = x_503;
x_457 = x_504;
x_458 = x_505;
x_459 = lean_box(0);
goto block_501;
}
}
else
{
lean_object* x_621; lean_object* x_622; uint8_t x_623; uint8_t x_628; 
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_621 = lean_ctor_get(x_549, 0);
x_628 = !lean_is_exclusive(x_549);
if (x_628 == 0)
{
x_622 = x_549;
x_623 = x_628;
goto block_627;
}
else
{
lean_inc(x_621);
lean_dec(x_549);
x_622 = lean_box(0);
x_623 = x_628;
goto block_627;
}
block_627:
{
lean_object* x_624; 
if (x_623 == 0)
{
x_624 = x_622;
goto block_625;
}
else
{
lean_object* x_626; 
x_626 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_626, 0, x_621);
x_624 = x_626;
goto block_625;
}
block_625:
{
return x_624;
}
}
}
}
}
else
{
lean_object* x_629; lean_object* x_630; uint8_t x_631; uint8_t x_636; 
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_629 = lean_ctor_get(x_507, 0);
x_636 = !lean_is_exclusive(x_507);
if (x_636 == 0)
{
x_630 = x_507;
x_631 = x_636;
goto block_635;
}
else
{
lean_inc(x_629);
lean_dec(x_507);
x_630 = lean_box(0);
x_631 = x_636;
goto block_635;
}
block_635:
{
lean_object* x_632; 
if (x_631 == 0)
{
x_632 = x_630;
goto block_633;
}
else
{
lean_object* x_634; 
x_634 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_634, 0, x_629);
x_632 = x_634;
goto block_633;
}
block_633:
{
return x_632;
}
}
}
}
}
else
{
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_79;
x_27 = lean_box(0);
goto block_32;
}
block_78:
{
lean_object* x_43; 
lean_inc(x_2);
x_43 = l_Lean_MVarId_getType(x_2, x_41, x_40, x_42, x_39);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_40);
x_46 = l_Lean_Meta_mkNoConfusion(x_44, x_45, x_41, x_40, x_42, x_39);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_47, x_40);
lean_dec(x_40);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_48);
x_49 = lean_box(x_12);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_49);
x_50 = x_35;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_49);
x_50 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_37);
x_17 = x_51;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_del_object(x_35);
lean_del_object(x_15);
lean_dec(x_14);
x_54 = lean_ctor_get(x_48, 0);
x_61 = !lean_is_exclusive(x_48);
if (x_61 == 0)
{
x_55 = x_48;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_40);
lean_del_object(x_35);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_62 = lean_ctor_get(x_46, 0);
x_69 = !lean_is_exclusive(x_46);
if (x_69 == 0)
{
x_63 = x_46;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_46);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_70 = lean_ctor_get(x_43, 0);
x_77 = !lean_is_exclusive(x_43);
if (x_77 == 0)
{
x_71 = x_43;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_43);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_70);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
block_101:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_1, 0);
x_86 = l_Lean_LocalDecl_fvarId(x_34);
lean_dec(x_34);
lean_inc(x_85);
lean_inc(x_2);
x_87 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_2, x_86, x_85, x_81, x_82, x_84, x_83);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_79;
x_27 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_90 = lean_box(x_12);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_37);
x_17 = x_92;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_100; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_93 = lean_ctor_get(x_87, 0);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
x_94 = x_87;
x_95 = x_100;
goto block_99;
}
else
{
lean_inc(x_93);
lean_dec(x_87);
x_94 = lean_box(0);
x_95 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_96; 
if (x_95 == 0)
{
x_96 = x_94;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
block_108:
{
if (x_107 == 0)
{
lean_dec_ref(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_79;
x_27 = lean_box(0);
goto block_32;
}
else
{
x_80 = lean_box(0);
x_81 = x_103;
x_82 = x_104;
x_83 = x_105;
x_84 = x_106;
goto block_101;
}
}
block_116:
{
if (x_112 == 0)
{
x_80 = lean_box(0);
x_81 = x_111;
x_82 = x_113;
x_83 = x_114;
x_84 = x_115;
goto block_101;
}
else
{
x_102 = lean_box(0);
x_103 = x_111;
x_104 = x_113;
x_105 = x_114;
x_106 = x_115;
x_107 = x_109;
goto block_108;
}
}
block_124:
{
if (x_123 == 0)
{
x_102 = lean_box(0);
x_103 = x_118;
x_104 = x_120;
x_105 = x_121;
x_106 = x_122;
x_107 = x_109;
goto block_108;
}
else
{
x_110 = lean_box(0);
x_111 = x_118;
x_112 = x_119;
x_113 = x_120;
x_114 = x_121;
x_115 = x_122;
goto block_116;
}
}
block_133:
{
uint8_t x_132; 
x_132 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_132 == 0)
{
x_117 = lean_box(0);
x_118 = x_127;
x_119 = x_125;
x_120 = x_128;
x_121 = x_130;
x_122 = x_129;
x_123 = x_109;
goto block_124;
}
else
{
if (x_126 == 0)
{
x_110 = lean_box(0);
x_111 = x_127;
x_112 = x_125;
x_113 = x_128;
x_114 = x_130;
x_115 = x_129;
goto block_116;
}
else
{
x_117 = lean_box(0);
x_118 = x_127;
x_119 = x_125;
x_120 = x_128;
x_121 = x_130;
x_122 = x_129;
x_123 = x_109;
goto block_124;
}
}
}
block_156:
{
if (x_141 == 0)
{
x_125 = x_136;
x_126 = x_137;
x_127 = x_138;
x_128 = x_135;
x_129 = x_139;
x_130 = x_134;
x_131 = lean_box(0);
goto block_133;
}
else
{
lean_object* x_142; 
lean_inc(x_134);
lean_inc_ref(x_139);
lean_inc(x_135);
lean_inc_ref(x_138);
lean_inc(x_34);
lean_inc(x_2);
x_142 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_2, x_34, x_138, x_135, x_139, x_134);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
x_125 = x_136;
x_126 = x_137;
x_127 = x_138;
x_128 = x_135;
x_129 = x_139;
x_130 = x_134;
x_131 = lean_box(0);
goto block_133;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec_ref(x_139);
lean_dec_ref(x_138);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_145 = lean_box(x_12);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_37);
x_17 = x_147;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_155; 
lean_dec_ref(x_139);
lean_dec_ref(x_138);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_148 = lean_ctor_get(x_142, 0);
x_155 = !lean_is_exclusive(x_142);
if (x_155 == 0)
{
x_149 = x_142;
x_150 = x_155;
goto block_154;
}
else
{
lean_inc(x_148);
lean_dec(x_142);
x_149 = lean_box(0);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_150 == 0)
{
x_151 = x_149;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_148);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
}
}
}
block_24:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_14);
x_20 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
block_32:
{
lean_object* x_28; size_t x_29; size_t x_30; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
x_29 = 1;
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
x_6 = x_28;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_704; 
x_14 = lean_ctor_get(x_6, 1);
x_704 = !lean_is_exclusive(x_6);
if (x_704 == 0)
{
lean_object* x_705; 
x_705 = lean_ctor_get(x_6, 0);
lean_dec(x_705);
x_15 = x_6;
x_16 = x_704;
goto block_703;
}
else
{
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_704;
goto block_703;
}
block_703:
{
lean_object* x_17; lean_object* x_18; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_33; 
x_25 = lean_box(0);
x_33 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_33) == 0)
{
lean_del_object(x_15);
x_26 = x_14;
x_27 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_702; 
x_34 = lean_ctor_get(x_33, 0);
x_702 = !lean_is_exclusive(x_33);
if (x_702 == 0)
{
x_35 = x_33;
x_36 = x_702;
goto block_701;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_702;
goto block_701;
}
block_701:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_134; uint8_t x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_37 = lean_box(0);
x_79 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
x_109 = l_Lean_LocalDecl_isImplementationDetail(x_34);
if (x_109 == 0)
{
lean_object* x_157; uint8_t x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_168; uint8_t x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_291; uint8_t x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; uint8_t x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; uint8_t x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; uint8_t x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_638; 
x_157 = l_Lean_LocalDecl_type(x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_157);
x_638 = l_Lean_Meta_matchNot_x3f(x_157, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
lean_dec_ref(x_638);
if (lean_obj_tag(x_639) == 1)
{
lean_object* x_640; lean_object* x_641; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
lean_dec_ref(x_639);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_641 = l_Lean_Meta_findLocalDeclWithType_x3f(x_640, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
lean_dec_ref(x_641);
if (lean_obj_tag(x_642) == 1)
{
lean_object* x_643; lean_object* x_644; uint8_t x_645; uint8_t x_684; 
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec_ref(x_1);
x_643 = lean_ctor_get(x_642, 0);
x_684 = !lean_is_exclusive(x_642);
if (x_684 == 0)
{
x_644 = x_642;
x_645 = x_684;
goto block_683;
}
else
{
lean_inc(x_643);
lean_dec(x_642);
x_644 = lean_box(0);
x_645 = x_684;
goto block_683;
}
block_683:
{
lean_object* x_646; 
lean_inc(x_2);
x_646 = l_Lean_MVarId_getType(x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
lean_dec_ref(x_646);
x_648 = l_Lean_LocalDecl_toExpr(x_34);
x_649 = l_Lean_mkFVar(x_643);
x_650 = l_Lean_Expr_app___override(x_648, x_649);
lean_inc(x_8);
x_651 = l_Lean_Meta_mkFalseElim(x_647, x_650, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
lean_dec_ref(x_651);
x_653 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_652, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; lean_object* x_655; 
lean_dec_ref(x_653);
x_654 = lean_box(x_12);
if (x_645 == 0)
{
lean_ctor_set(x_644, 0, x_654);
x_655 = x_644;
goto block_657;
}
else
{
lean_object* x_658; 
x_658 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_658, 0, x_654);
x_655 = x_658;
goto block_657;
}
block_657:
{
lean_object* x_656; 
x_656 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_37);
x_17 = x_656;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_659; lean_object* x_660; uint8_t x_661; uint8_t x_666; 
lean_del_object(x_644);
lean_del_object(x_15);
lean_dec(x_14);
x_659 = lean_ctor_get(x_653, 0);
x_666 = !lean_is_exclusive(x_653);
if (x_666 == 0)
{
x_660 = x_653;
x_661 = x_666;
goto block_665;
}
else
{
lean_inc(x_659);
lean_dec(x_653);
x_660 = lean_box(0);
x_661 = x_666;
goto block_665;
}
block_665:
{
lean_object* x_662; 
if (x_661 == 0)
{
x_662 = x_660;
goto block_663;
}
else
{
lean_object* x_664; 
x_664 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_664, 0, x_659);
x_662 = x_664;
goto block_663;
}
block_663:
{
return x_662;
}
}
}
}
else
{
lean_object* x_667; lean_object* x_668; uint8_t x_669; uint8_t x_674; 
lean_del_object(x_644);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
x_667 = lean_ctor_get(x_651, 0);
x_674 = !lean_is_exclusive(x_651);
if (x_674 == 0)
{
x_668 = x_651;
x_669 = x_674;
goto block_673;
}
else
{
lean_inc(x_667);
lean_dec(x_651);
x_668 = lean_box(0);
x_669 = x_674;
goto block_673;
}
block_673:
{
lean_object* x_670; 
if (x_669 == 0)
{
x_670 = x_668;
goto block_671;
}
else
{
lean_object* x_672; 
x_672 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_672, 0, x_667);
x_670 = x_672;
goto block_671;
}
block_671:
{
return x_670;
}
}
}
}
else
{
lean_object* x_675; lean_object* x_676; uint8_t x_677; uint8_t x_682; 
lean_del_object(x_644);
lean_dec(x_643);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_675 = lean_ctor_get(x_646, 0);
x_682 = !lean_is_exclusive(x_646);
if (x_682 == 0)
{
x_676 = x_646;
x_677 = x_682;
goto block_681;
}
else
{
lean_inc(x_675);
lean_dec(x_646);
x_676 = lean_box(0);
x_677 = x_682;
goto block_681;
}
block_681:
{
lean_object* x_678; 
if (x_677 == 0)
{
x_678 = x_676;
goto block_679;
}
else
{
lean_object* x_680; 
x_680 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_680, 0, x_675);
x_678 = x_680;
goto block_679;
}
block_679:
{
return x_678;
}
}
}
}
}
else
{
lean_dec(x_642);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_502 = x_7;
x_503 = x_8;
x_504 = x_9;
x_505 = x_10;
x_506 = lean_box(0);
goto block_637;
}
}
else
{
lean_object* x_685; lean_object* x_686; uint8_t x_687; uint8_t x_692; 
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_685 = lean_ctor_get(x_641, 0);
x_692 = !lean_is_exclusive(x_641);
if (x_692 == 0)
{
x_686 = x_641;
x_687 = x_692;
goto block_691;
}
else
{
lean_inc(x_685);
lean_dec(x_641);
x_686 = lean_box(0);
x_687 = x_692;
goto block_691;
}
block_691:
{
lean_object* x_688; 
if (x_687 == 0)
{
x_688 = x_686;
goto block_689;
}
else
{
lean_object* x_690; 
x_690 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_690, 0, x_685);
x_688 = x_690;
goto block_689;
}
block_689:
{
return x_688;
}
}
}
}
else
{
lean_dec(x_639);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_502 = x_7;
x_503 = x_8;
x_504 = x_9;
x_505 = x_10;
x_506 = lean_box(0);
goto block_637;
}
}
else
{
lean_object* x_693; lean_object* x_694; uint8_t x_695; uint8_t x_700; 
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_693 = lean_ctor_get(x_638, 0);
x_700 = !lean_is_exclusive(x_638);
if (x_700 == 0)
{
x_694 = x_638;
x_695 = x_700;
goto block_699;
}
else
{
lean_inc(x_693);
lean_dec(x_638);
x_694 = lean_box(0);
x_695 = x_700;
goto block_699;
}
block_699:
{
lean_object* x_696; 
if (x_695 == 0)
{
x_696 = x_694;
goto block_697;
}
else
{
lean_object* x_698; 
x_698 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_698, 0, x_693);
x_696 = x_698;
goto block_697;
}
block_697:
{
return x_696;
}
}
}
block_167:
{
uint8_t x_165; 
x_165 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_165 == 0)
{
lean_dec_ref(x_157);
x_134 = x_160;
x_135 = x_158;
x_136 = x_159;
x_137 = x_161;
x_138 = lean_box(0);
x_139 = x_162;
x_140 = x_163;
x_141 = x_109;
goto block_156;
}
else
{
uint8_t x_166; 
x_166 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_157);
x_134 = x_160;
x_135 = x_158;
x_136 = x_159;
x_137 = x_161;
x_138 = lean_box(0);
x_139 = x_162;
x_140 = x_163;
x_141 = x_166;
goto block_156;
}
}
block_178:
{
if (x_176 == 0)
{
lean_dec_ref(x_168);
x_158 = x_169;
x_159 = x_170;
x_160 = x_173;
x_161 = x_172;
x_162 = x_174;
x_163 = x_171;
x_164 = lean_box(0);
goto block_167;
}
else
{
lean_object* x_177; 
lean_dec_ref(x_174);
lean_dec_ref(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_168);
return x_177;
}
}
block_189:
{
uint8_t x_187; 
x_187 = l_Lean_Exception_isInterrupt(x_185);
if (x_187 == 0)
{
uint8_t x_188; 
lean_inc_ref(x_185);
x_188 = l_Lean_Exception_isRuntime(x_185);
x_168 = x_185;
x_169 = x_179;
x_170 = x_180;
x_171 = x_181;
x_172 = x_183;
x_173 = x_182;
x_174 = x_184;
x_175 = lean_box(0);
x_176 = x_188;
goto block_178;
}
else
{
x_168 = x_185;
x_169 = x_179;
x_170 = x_180;
x_171 = x_181;
x_172 = x_183;
x_173 = x_182;
x_174 = x_184;
x_175 = lean_box(0);
x_176 = x_187;
goto block_178;
}
}
block_281:
{
lean_object* x_197; 
lean_inc(x_192);
lean_inc_ref(x_195);
lean_inc(x_193);
lean_inc_ref(x_194);
lean_inc_ref(x_157);
x_197 = l_Lean_Meta_mkDecide(x_157, x_194, x_193, x_195, x_192);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; lean_object* x_218; uint8_t x_219; uint8_t x_279; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec_ref(x_197);
x_199 = l_Lean_Meta_Context_config(x_194);
x_200 = lean_ctor_get_uint8(x_199, 0);
x_201 = lean_ctor_get_uint8(x_199, 1);
x_202 = lean_ctor_get_uint8(x_199, 2);
x_203 = lean_ctor_get_uint8(x_199, 3);
x_204 = lean_ctor_get_uint8(x_199, 4);
x_205 = lean_ctor_get_uint8(x_199, 5);
x_206 = lean_ctor_get_uint8(x_199, 6);
x_207 = lean_ctor_get_uint8(x_199, 7);
x_208 = lean_ctor_get_uint8(x_199, 8);
x_209 = lean_ctor_get_uint8(x_199, 10);
x_210 = lean_ctor_get_uint8(x_199, 11);
x_211 = lean_ctor_get_uint8(x_199, 12);
x_212 = lean_ctor_get_uint8(x_199, 13);
x_213 = lean_ctor_get_uint8(x_199, 14);
x_214 = lean_ctor_get_uint8(x_199, 15);
x_215 = lean_ctor_get_uint8(x_199, 16);
x_216 = lean_ctor_get_uint8(x_199, 17);
x_217 = lean_ctor_get_uint8(x_199, 18);
x_279 = !lean_is_exclusive(x_199);
if (x_279 == 0)
{
x_218 = x_199;
x_219 = x_279;
goto block_278;
}
else
{
lean_dec(x_199);
x_218 = lean_box(0);
x_219 = x_279;
goto block_278;
}
block_278:
{
uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; uint8_t x_228; uint8_t x_229; uint8_t x_230; lean_object* x_231; 
x_220 = lean_ctor_get_uint8(x_194, sizeof(void*)*7);
x_221 = lean_ctor_get(x_194, 1);
x_222 = lean_ctor_get(x_194, 2);
x_223 = lean_ctor_get(x_194, 3);
x_224 = lean_ctor_get(x_194, 4);
x_225 = lean_ctor_get(x_194, 5);
x_226 = lean_ctor_get(x_194, 6);
x_227 = lean_ctor_get_uint8(x_194, sizeof(void*)*7 + 1);
x_228 = lean_ctor_get_uint8(x_194, sizeof(void*)*7 + 2);
x_229 = lean_ctor_get_uint8(x_194, sizeof(void*)*7 + 3);
x_230 = 1;
if (x_219 == 0)
{
x_231 = x_218;
goto block_276;
}
else
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_277, 0, x_200);
lean_ctor_set_uint8(x_277, 1, x_201);
lean_ctor_set_uint8(x_277, 2, x_202);
lean_ctor_set_uint8(x_277, 3, x_203);
lean_ctor_set_uint8(x_277, 4, x_204);
lean_ctor_set_uint8(x_277, 5, x_205);
lean_ctor_set_uint8(x_277, 6, x_206);
lean_ctor_set_uint8(x_277, 7, x_207);
lean_ctor_set_uint8(x_277, 8, x_208);
lean_ctor_set_uint8(x_277, 10, x_209);
lean_ctor_set_uint8(x_277, 11, x_210);
lean_ctor_set_uint8(x_277, 12, x_211);
lean_ctor_set_uint8(x_277, 13, x_212);
lean_ctor_set_uint8(x_277, 14, x_213);
lean_ctor_set_uint8(x_277, 15, x_214);
lean_ctor_set_uint8(x_277, 16, x_215);
lean_ctor_set_uint8(x_277, 17, x_216);
lean_ctor_set_uint8(x_277, 18, x_217);
x_231 = x_277;
goto block_276;
}
block_276:
{
uint64_t x_232; uint64_t x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_ctor_set_uint8(x_231, 9, x_230);
x_232 = l_Lean_Meta_Context_configKey(x_194);
x_233 = 2;
x_234 = lean_uint64_shift_right(x_232, x_233);
x_235 = lean_uint64_shift_left(x_234, x_233);
x_236 = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
x_237 = lean_uint64_lor(x_235, x_236);
x_238 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_238, 0, x_231);
lean_ctor_set_uint64(x_238, sizeof(void*)*1, x_237);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_224);
lean_inc_ref(x_223);
lean_inc_ref(x_222);
lean_inc(x_221);
x_239 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_221);
lean_ctor_set(x_239, 2, x_222);
lean_ctor_set(x_239, 3, x_223);
lean_ctor_set(x_239, 4, x_224);
lean_ctor_set(x_239, 5, x_225);
lean_ctor_set(x_239, 6, x_226);
lean_ctor_set_uint8(x_239, sizeof(void*)*7, x_220);
lean_ctor_set_uint8(x_239, sizeof(void*)*7 + 1, x_227);
lean_ctor_set_uint8(x_239, sizeof(void*)*7 + 2, x_228);
lean_ctor_set_uint8(x_239, sizeof(void*)*7 + 3, x_229);
lean_inc(x_192);
lean_inc_ref(x_195);
lean_inc(x_193);
lean_inc(x_198);
x_240 = lean_whnf(x_198, x_239, x_193, x_195, x_192);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
lean_dec_ref(x_240);
x_242 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
x_243 = l_Lean_Expr_isConstOf(x_241, x_242);
lean_dec(x_241);
if (x_243 == 0)
{
lean_dec(x_198);
x_158 = x_190;
x_159 = x_191;
x_160 = x_194;
x_161 = x_193;
x_162 = x_195;
x_163 = x_192;
x_164 = lean_box(0);
goto block_167;
}
else
{
lean_object* x_244; 
lean_inc(x_192);
lean_inc_ref(x_195);
lean_inc(x_193);
lean_inc_ref(x_194);
lean_inc(x_198);
x_244 = l_Lean_Meta_mkEqRefl(x_198, x_194, x_193, x_195, x_192);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec_ref(x_244);
lean_inc(x_2);
x_246 = l_Lean_MVarId_getType(x_2, x_194, x_193, x_195, x_192);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
x_248 = l_Lean_Expr_getAppNumArgs(x_198);
x_249 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
x_250 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(x_248);
x_251 = lean_mk_array(x_248, x_250);
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_nat_sub(x_248, x_252);
lean_dec(x_248);
x_254 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_198, x_251, x_253);
x_255 = lean_array_push(x_254, x_245);
x_256 = l_Lean_mkAppN(x_249, x_255);
lean_dec_ref(x_255);
lean_inc(x_34);
x_257 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_192);
lean_inc_ref(x_195);
lean_inc(x_193);
lean_inc_ref(x_194);
x_258 = l_Lean_Meta_mkAbsurd(x_247, x_257, x_256, x_194, x_193, x_195, x_192);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
lean_inc(x_2);
x_260 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_259, x_193);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; uint8_t x_262; uint8_t x_269; 
lean_dec_ref(x_195);
lean_dec_ref(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_269 = !lean_is_exclusive(x_260);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_260, 0);
lean_dec(x_270);
x_261 = x_260;
x_262 = x_269;
goto block_268;
}
else
{
lean_dec(x_260);
x_261 = lean_box(0);
x_262 = x_269;
goto block_268;
}
block_268:
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_box(x_12);
if (x_262 == 0)
{
lean_ctor_set_tag(x_261, 1);
lean_ctor_set(x_261, 0, x_263);
x_264 = x_261;
goto block_266;
}
else
{
lean_object* x_267; 
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_263);
x_264 = x_267;
goto block_266;
}
block_266:
{
lean_object* x_265; 
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_37);
x_17 = x_265;
x_18 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_260, 0);
lean_inc(x_271);
lean_dec_ref(x_260);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_194;
x_183 = x_193;
x_184 = x_195;
x_185 = x_271;
x_186 = lean_box(0);
goto block_189;
}
}
else
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_258, 0);
lean_inc(x_272);
lean_dec_ref(x_258);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_194;
x_183 = x_193;
x_184 = x_195;
x_185 = x_272;
x_186 = lean_box(0);
goto block_189;
}
}
else
{
lean_object* x_273; 
lean_dec(x_245);
lean_dec(x_198);
x_273 = lean_ctor_get(x_246, 0);
lean_inc(x_273);
lean_dec_ref(x_246);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_194;
x_183 = x_193;
x_184 = x_195;
x_185 = x_273;
x_186 = lean_box(0);
goto block_189;
}
}
else
{
lean_object* x_274; 
lean_dec(x_198);
x_274 = lean_ctor_get(x_244, 0);
lean_inc(x_274);
lean_dec_ref(x_244);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_194;
x_183 = x_193;
x_184 = x_195;
x_185 = x_274;
x_186 = lean_box(0);
goto block_189;
}
}
}
else
{
lean_object* x_275; 
lean_dec(x_198);
x_275 = lean_ctor_get(x_240, 0);
lean_inc(x_275);
lean_dec_ref(x_240);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_194;
x_183 = x_193;
x_184 = x_195;
x_185 = x_275;
x_186 = lean_box(0);
goto block_189;
}
}
}
}
else
{
lean_object* x_280; 
x_280 = lean_ctor_get(x_197, 0);
lean_inc(x_280);
lean_dec_ref(x_197);
x_179 = x_190;
x_180 = x_191;
x_181 = x_192;
x_182 = x_194;
x_183 = x_193;
x_184 = x_195;
x_185 = x_280;
x_186 = lean_box(0);
goto block_189;
}
}
block_290:
{
if (x_289 == 0)
{
x_158 = x_282;
x_159 = x_283;
x_160 = x_286;
x_161 = x_285;
x_162 = x_287;
x_163 = x_284;
x_164 = lean_box(0);
goto block_167;
}
else
{
x_190 = x_282;
x_191 = x_283;
x_192 = x_284;
x_193 = x_285;
x_194 = x_286;
x_195 = x_287;
x_196 = lean_box(0);
goto block_281;
}
}
block_301:
{
if (x_299 == 0)
{
lean_dec_ref(x_291);
x_282 = x_292;
x_283 = x_293;
x_284 = x_294;
x_285 = x_296;
x_286 = x_295;
x_287 = x_297;
x_288 = lean_box(0);
x_289 = x_109;
goto block_290;
}
else
{
uint8_t x_300; 
x_300 = l_Lean_Expr_hasFVar(x_291);
lean_dec_ref(x_291);
if (x_300 == 0)
{
x_190 = x_292;
x_191 = x_293;
x_192 = x_294;
x_193 = x_296;
x_194 = x_295;
x_195 = x_297;
x_196 = lean_box(0);
goto block_281;
}
else
{
x_282 = x_292;
x_283 = x_293;
x_284 = x_294;
x_285 = x_296;
x_286 = x_295;
x_287 = x_297;
x_288 = lean_box(0);
x_289 = x_109;
goto block_290;
}
}
}
block_321:
{
lean_object* x_310; 
lean_inc_ref(x_157);
x_310 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_157, x_307);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; uint8_t x_312; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
lean_dec_ref(x_310);
x_312 = l_Lean_Expr_hasMVar(x_311);
if (x_312 == 0)
{
x_291 = x_311;
x_292 = x_302;
x_293 = x_303;
x_294 = x_304;
x_295 = x_306;
x_296 = x_307;
x_297 = x_308;
x_298 = lean_box(0);
x_299 = x_309;
goto block_301;
}
else
{
x_291 = x_311;
x_292 = x_302;
x_293 = x_303;
x_294 = x_304;
x_295 = x_306;
x_296 = x_307;
x_297 = x_308;
x_298 = lean_box(0);
x_299 = x_109;
goto block_301;
}
}
else
{
lean_object* x_313; lean_object* x_314; uint8_t x_315; uint8_t x_320; 
lean_dec_ref(x_308);
lean_dec(x_307);
lean_dec_ref(x_306);
lean_dec(x_304);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_313 = lean_ctor_get(x_310, 0);
x_320 = !lean_is_exclusive(x_310);
if (x_320 == 0)
{
x_314 = x_310;
x_315 = x_320;
goto block_319;
}
else
{
lean_inc(x_313);
lean_dec(x_310);
x_314 = lean_box(0);
x_315 = x_320;
goto block_319;
}
block_319:
{
lean_object* x_316; 
if (x_315 == 0)
{
x_316 = x_314;
goto block_317;
}
else
{
lean_object* x_318; 
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_313);
x_316 = x_318;
goto block_317;
}
block_317:
{
return x_316;
}
}
}
}
block_330:
{
if (x_329 == 0)
{
x_158 = x_322;
x_159 = x_323;
x_160 = x_327;
x_161 = x_326;
x_162 = x_328;
x_163 = x_325;
x_164 = lean_box(0);
goto block_167;
}
else
{
x_302 = x_322;
x_303 = x_323;
x_304 = x_325;
x_305 = lean_box(0);
x_306 = x_327;
x_307 = x_326;
x_308 = x_328;
x_309 = x_329;
goto block_321;
}
}
block_340:
{
uint8_t x_338; 
x_338 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_338 == 0)
{
x_322 = x_332;
x_323 = x_331;
x_324 = lean_box(0);
x_325 = x_336;
x_326 = x_334;
x_327 = x_333;
x_328 = x_335;
x_329 = x_109;
goto block_330;
}
else
{
uint8_t x_339; 
x_339 = l_Lean_Expr_hasFVar(x_157);
if (x_339 == 0)
{
x_302 = x_332;
x_303 = x_331;
x_304 = x_336;
x_305 = lean_box(0);
x_306 = x_333;
x_307 = x_334;
x_308 = x_335;
x_309 = x_338;
goto block_321;
}
else
{
x_322 = x_332;
x_323 = x_331;
x_324 = lean_box(0);
x_325 = x_336;
x_326 = x_334;
x_327 = x_333;
x_328 = x_335;
x_329 = x_109;
goto block_330;
}
}
}
block_403:
{
lean_object* x_349; 
lean_inc(x_344);
lean_inc_ref(x_342);
lean_inc(x_341);
lean_inc_ref(x_345);
x_349 = l_Lean_Meta_isExprDefEq(x_347, x_348, x_345, x_341, x_342, x_344);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; uint8_t x_351; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
lean_dec_ref(x_349);
x_351 = lean_unbox(x_350);
lean_dec(x_350);
if (x_351 == 0)
{
x_331 = x_343;
x_332 = x_12;
x_333 = x_345;
x_334 = x_341;
x_335 = x_342;
x_336 = x_344;
x_337 = lean_box(0);
goto block_340;
}
else
{
lean_object* x_352; 
lean_dec_ref(x_157);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_352 = l_Lean_MVarId_getType(x_2, x_345, x_341, x_342, x_344);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec_ref(x_352);
x_354 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_344);
lean_inc_ref(x_342);
lean_inc(x_341);
lean_inc_ref(x_345);
x_355 = l_Lean_Meta_mkEqOfHEq(x_354, x_12, x_345, x_341, x_342, x_344);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
lean_dec_ref(x_355);
lean_inc(x_341);
x_357 = l_Lean_Meta_mkNoConfusion(x_353, x_356, x_345, x_341, x_342, x_344);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
lean_dec_ref(x_357);
x_359 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_358, x_341);
lean_dec(x_341);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec_ref(x_359);
x_360 = lean_box(x_12);
x_361 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_361, 0, x_360);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_37);
x_17 = x_362;
x_18 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_363; lean_object* x_364; uint8_t x_365; uint8_t x_370; 
lean_del_object(x_15);
lean_dec(x_14);
x_363 = lean_ctor_get(x_359, 0);
x_370 = !lean_is_exclusive(x_359);
if (x_370 == 0)
{
x_364 = x_359;
x_365 = x_370;
goto block_369;
}
else
{
lean_inc(x_363);
lean_dec(x_359);
x_364 = lean_box(0);
x_365 = x_370;
goto block_369;
}
block_369:
{
lean_object* x_366; 
if (x_365 == 0)
{
x_366 = x_364;
goto block_367;
}
else
{
lean_object* x_368; 
x_368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_368, 0, x_363);
x_366 = x_368;
goto block_367;
}
block_367:
{
return x_366;
}
}
}
}
else
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; uint8_t x_378; 
lean_dec(x_341);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_371 = lean_ctor_get(x_357, 0);
x_378 = !lean_is_exclusive(x_357);
if (x_378 == 0)
{
x_372 = x_357;
x_373 = x_378;
goto block_377;
}
else
{
lean_inc(x_371);
lean_dec(x_357);
x_372 = lean_box(0);
x_373 = x_378;
goto block_377;
}
block_377:
{
lean_object* x_374; 
if (x_373 == 0)
{
x_374 = x_372;
goto block_375;
}
else
{
lean_object* x_376; 
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_371);
x_374 = x_376;
goto block_375;
}
block_375:
{
return x_374;
}
}
}
}
else
{
lean_object* x_379; lean_object* x_380; uint8_t x_381; uint8_t x_386; 
lean_dec(x_353);
lean_dec_ref(x_345);
lean_dec(x_344);
lean_dec_ref(x_342);
lean_dec(x_341);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_379 = lean_ctor_get(x_355, 0);
x_386 = !lean_is_exclusive(x_355);
if (x_386 == 0)
{
x_380 = x_355;
x_381 = x_386;
goto block_385;
}
else
{
lean_inc(x_379);
lean_dec(x_355);
x_380 = lean_box(0);
x_381 = x_386;
goto block_385;
}
block_385:
{
lean_object* x_382; 
if (x_381 == 0)
{
x_382 = x_380;
goto block_383;
}
else
{
lean_object* x_384; 
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_379);
x_382 = x_384;
goto block_383;
}
block_383:
{
return x_382;
}
}
}
}
else
{
lean_object* x_387; lean_object* x_388; uint8_t x_389; uint8_t x_394; 
lean_dec_ref(x_345);
lean_dec(x_344);
lean_dec_ref(x_342);
lean_dec(x_341);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_387 = lean_ctor_get(x_352, 0);
x_394 = !lean_is_exclusive(x_352);
if (x_394 == 0)
{
x_388 = x_352;
x_389 = x_394;
goto block_393;
}
else
{
lean_inc(x_387);
lean_dec(x_352);
x_388 = lean_box(0);
x_389 = x_394;
goto block_393;
}
block_393:
{
lean_object* x_390; 
if (x_389 == 0)
{
x_390 = x_388;
goto block_391;
}
else
{
lean_object* x_392; 
x_392 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_392, 0, x_387);
x_390 = x_392;
goto block_391;
}
block_391:
{
return x_390;
}
}
}
}
}
else
{
lean_object* x_395; lean_object* x_396; uint8_t x_397; uint8_t x_402; 
lean_dec_ref(x_345);
lean_dec(x_344);
lean_dec_ref(x_342);
lean_dec(x_341);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_395 = lean_ctor_get(x_349, 0);
x_402 = !lean_is_exclusive(x_349);
if (x_402 == 0)
{
x_396 = x_349;
x_397 = x_402;
goto block_401;
}
else
{
lean_inc(x_395);
lean_dec(x_349);
x_396 = lean_box(0);
x_397 = x_402;
goto block_401;
}
block_401:
{
lean_object* x_398; 
if (x_397 == 0)
{
x_398 = x_396;
goto block_399;
}
else
{
lean_object* x_400; 
x_400 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_400, 0, x_395);
x_398 = x_400;
goto block_399;
}
block_399:
{
return x_398;
}
}
}
}
block_454:
{
lean_object* x_410; 
lean_inc(x_408);
lean_inc_ref(x_407);
lean_inc(x_406);
lean_inc_ref(x_405);
lean_inc_ref(x_157);
x_410 = l_Lean_Meta_matchHEq_x3f(x_157, x_405, x_406, x_407, x_408);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
lean_dec_ref(x_410);
if (lean_obj_tag(x_411) == 1)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
lean_dec_ref(x_411);
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_412, 0);
lean_inc(x_415);
lean_dec(x_412);
x_416 = lean_ctor_get(x_413, 0);
lean_inc(x_416);
lean_dec(x_413);
x_417 = lean_ctor_get(x_414, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_414, 1);
lean_inc(x_418);
lean_dec(x_414);
lean_inc(x_408);
lean_inc_ref(x_407);
lean_inc(x_406);
lean_inc_ref(x_405);
x_419 = l_Lean_Meta_matchConstructorApp_x3f(x_416, x_405, x_406, x_407, x_408);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
lean_dec_ref(x_419);
if (lean_obj_tag(x_420) == 1)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
lean_dec_ref(x_420);
lean_inc(x_408);
lean_inc_ref(x_407);
lean_inc(x_406);
lean_inc_ref(x_405);
x_422 = l_Lean_Meta_matchConstructorApp_x3f(x_418, x_405, x_406, x_407, x_408);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
lean_dec_ref(x_422);
if (lean_obj_tag(x_423) == 1)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_424 = lean_ctor_get(x_421, 0);
lean_inc_ref(x_424);
lean_dec(x_421);
x_425 = lean_ctor_get(x_423, 0);
lean_inc(x_425);
lean_dec_ref(x_423);
x_426 = lean_ctor_get(x_425, 0);
lean_inc_ref(x_426);
lean_dec(x_425);
x_427 = lean_ctor_get(x_424, 0);
lean_inc(x_427);
lean_dec_ref(x_424);
x_428 = lean_ctor_get(x_426, 0);
lean_inc(x_428);
lean_dec_ref(x_426);
x_429 = lean_name_eq(x_427, x_428);
lean_dec(x_428);
lean_dec(x_427);
if (x_429 == 0)
{
x_341 = x_406;
x_342 = x_407;
x_343 = x_404;
x_344 = x_408;
x_345 = x_405;
x_346 = lean_box(0);
x_347 = x_415;
x_348 = x_417;
goto block_403;
}
else
{
if (x_109 == 0)
{
lean_dec(x_417);
lean_dec(x_415);
x_331 = x_404;
x_332 = x_12;
x_333 = x_405;
x_334 = x_406;
x_335 = x_407;
x_336 = x_408;
x_337 = lean_box(0);
goto block_340;
}
else
{
x_341 = x_406;
x_342 = x_407;
x_343 = x_404;
x_344 = x_408;
x_345 = x_405;
x_346 = lean_box(0);
x_347 = x_415;
x_348 = x_417;
goto block_403;
}
}
}
else
{
lean_dec(x_423);
lean_dec(x_421);
lean_dec(x_417);
lean_dec(x_415);
x_331 = x_404;
x_332 = x_12;
x_333 = x_405;
x_334 = x_406;
x_335 = x_407;
x_336 = x_408;
x_337 = lean_box(0);
goto block_340;
}
}
else
{
lean_object* x_430; lean_object* x_431; uint8_t x_432; uint8_t x_437; 
lean_dec(x_421);
lean_dec(x_417);
lean_dec(x_415);
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
lean_dec_ref(x_405);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_430 = lean_ctor_get(x_422, 0);
x_437 = !lean_is_exclusive(x_422);
if (x_437 == 0)
{
x_431 = x_422;
x_432 = x_437;
goto block_436;
}
else
{
lean_inc(x_430);
lean_dec(x_422);
x_431 = lean_box(0);
x_432 = x_437;
goto block_436;
}
block_436:
{
lean_object* x_433; 
if (x_432 == 0)
{
x_433 = x_431;
goto block_434;
}
else
{
lean_object* x_435; 
x_435 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_435, 0, x_430);
x_433 = x_435;
goto block_434;
}
block_434:
{
return x_433;
}
}
}
}
else
{
lean_dec(x_420);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_415);
x_331 = x_404;
x_332 = x_12;
x_333 = x_405;
x_334 = x_406;
x_335 = x_407;
x_336 = x_408;
x_337 = lean_box(0);
goto block_340;
}
}
else
{
lean_object* x_438; lean_object* x_439; uint8_t x_440; uint8_t x_445; 
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_415);
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
lean_dec_ref(x_405);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_438 = lean_ctor_get(x_419, 0);
x_445 = !lean_is_exclusive(x_419);
if (x_445 == 0)
{
x_439 = x_419;
x_440 = x_445;
goto block_444;
}
else
{
lean_inc(x_438);
lean_dec(x_419);
x_439 = lean_box(0);
x_440 = x_445;
goto block_444;
}
block_444:
{
lean_object* x_441; 
if (x_440 == 0)
{
x_441 = x_439;
goto block_442;
}
else
{
lean_object* x_443; 
x_443 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_443, 0, x_438);
x_441 = x_443;
goto block_442;
}
block_442:
{
return x_441;
}
}
}
}
else
{
lean_dec(x_411);
x_331 = x_404;
x_332 = x_109;
x_333 = x_405;
x_334 = x_406;
x_335 = x_407;
x_336 = x_408;
x_337 = lean_box(0);
goto block_340;
}
}
else
{
lean_object* x_446; lean_object* x_447; uint8_t x_448; uint8_t x_453; 
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
lean_dec_ref(x_405);
lean_dec_ref(x_157);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_446 = lean_ctor_get(x_410, 0);
x_453 = !lean_is_exclusive(x_410);
if (x_453 == 0)
{
x_447 = x_410;
x_448 = x_453;
goto block_452;
}
else
{
lean_inc(x_446);
lean_dec(x_410);
x_447 = lean_box(0);
x_448 = x_453;
goto block_452;
}
block_452:
{
lean_object* x_449; 
if (x_448 == 0)
{
x_449 = x_447;
goto block_450;
}
else
{
lean_object* x_451; 
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_446);
x_449 = x_451;
goto block_450;
}
block_450:
{
return x_449;
}
}
}
}
block_501:
{
lean_object* x_460; 
lean_inc(x_458);
lean_inc_ref(x_457);
lean_inc(x_456);
lean_inc_ref(x_455);
lean_inc_ref(x_157);
x_460 = l_Lean_Meta_matchEq_x3f(x_157, x_455, x_456, x_457, x_458);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
lean_dec_ref(x_460);
if (lean_obj_tag(x_461) == 1)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
lean_dec_ref(x_461);
x_463 = lean_ctor_get(x_462, 1);
lean_inc(x_463);
lean_dec(x_462);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
lean_inc(x_458);
lean_inc_ref(x_457);
lean_inc(x_456);
lean_inc_ref(x_455);
x_466 = l_Lean_Meta_matchConstructorApp_x3f(x_464, x_455, x_456, x_457, x_458);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
lean_dec_ref(x_466);
if (lean_obj_tag(x_467) == 1)
{
lean_object* x_468; lean_object* x_469; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
lean_dec_ref(x_467);
lean_inc(x_458);
lean_inc_ref(x_457);
lean_inc(x_456);
lean_inc_ref(x_455);
x_469 = l_Lean_Meta_matchConstructorApp_x3f(x_465, x_455, x_456, x_457, x_458);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
lean_dec_ref(x_469);
if (lean_obj_tag(x_470) == 1)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_471 = lean_ctor_get(x_468, 0);
lean_inc_ref(x_471);
lean_dec(x_468);
x_472 = lean_ctor_get(x_470, 0);
lean_inc(x_472);
lean_dec_ref(x_470);
x_473 = lean_ctor_get(x_472, 0);
lean_inc_ref(x_473);
lean_dec(x_472);
x_474 = lean_ctor_get(x_471, 0);
lean_inc(x_474);
lean_dec_ref(x_471);
x_475 = lean_ctor_get(x_473, 0);
lean_inc(x_475);
lean_dec_ref(x_473);
x_476 = lean_name_eq(x_474, x_475);
lean_dec(x_475);
lean_dec(x_474);
if (x_476 == 0)
{
lean_dec_ref(x_157);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_38 = x_455;
x_39 = lean_box(0);
x_40 = x_457;
x_41 = x_456;
x_42 = x_458;
goto block_78;
}
else
{
if (x_109 == 0)
{
lean_del_object(x_35);
x_404 = x_12;
x_405 = x_455;
x_406 = x_456;
x_407 = x_457;
x_408 = x_458;
x_409 = lean_box(0);
goto block_454;
}
else
{
lean_dec_ref(x_157);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_38 = x_455;
x_39 = lean_box(0);
x_40 = x_457;
x_41 = x_456;
x_42 = x_458;
goto block_78;
}
}
}
else
{
lean_dec(x_470);
lean_dec(x_468);
lean_del_object(x_35);
x_404 = x_12;
x_405 = x_455;
x_406 = x_456;
x_407 = x_457;
x_408 = x_458;
x_409 = lean_box(0);
goto block_454;
}
}
else
{
lean_object* x_477; lean_object* x_478; uint8_t x_479; uint8_t x_484; 
lean_dec(x_468);
lean_dec(x_458);
lean_dec_ref(x_457);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_477 = lean_ctor_get(x_469, 0);
x_484 = !lean_is_exclusive(x_469);
if (x_484 == 0)
{
x_478 = x_469;
x_479 = x_484;
goto block_483;
}
else
{
lean_inc(x_477);
lean_dec(x_469);
x_478 = lean_box(0);
x_479 = x_484;
goto block_483;
}
block_483:
{
lean_object* x_480; 
if (x_479 == 0)
{
x_480 = x_478;
goto block_481;
}
else
{
lean_object* x_482; 
x_482 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_482, 0, x_477);
x_480 = x_482;
goto block_481;
}
block_481:
{
return x_480;
}
}
}
}
else
{
lean_dec(x_467);
lean_dec(x_465);
lean_del_object(x_35);
x_404 = x_12;
x_405 = x_455;
x_406 = x_456;
x_407 = x_457;
x_408 = x_458;
x_409 = lean_box(0);
goto block_454;
}
}
else
{
lean_object* x_485; lean_object* x_486; uint8_t x_487; uint8_t x_492; 
lean_dec(x_465);
lean_dec(x_458);
lean_dec_ref(x_457);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_485 = lean_ctor_get(x_466, 0);
x_492 = !lean_is_exclusive(x_466);
if (x_492 == 0)
{
x_486 = x_466;
x_487 = x_492;
goto block_491;
}
else
{
lean_inc(x_485);
lean_dec(x_466);
x_486 = lean_box(0);
x_487 = x_492;
goto block_491;
}
block_491:
{
lean_object* x_488; 
if (x_487 == 0)
{
x_488 = x_486;
goto block_489;
}
else
{
lean_object* x_490; 
x_490 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_490, 0, x_485);
x_488 = x_490;
goto block_489;
}
block_489:
{
return x_488;
}
}
}
}
else
{
lean_dec(x_461);
lean_del_object(x_35);
x_404 = x_109;
x_405 = x_455;
x_406 = x_456;
x_407 = x_457;
x_408 = x_458;
x_409 = lean_box(0);
goto block_454;
}
}
else
{
lean_object* x_493; lean_object* x_494; uint8_t x_495; uint8_t x_500; 
lean_dec(x_458);
lean_dec_ref(x_457);
lean_dec(x_456);
lean_dec_ref(x_455);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_493 = lean_ctor_get(x_460, 0);
x_500 = !lean_is_exclusive(x_460);
if (x_500 == 0)
{
x_494 = x_460;
x_495 = x_500;
goto block_499;
}
else
{
lean_inc(x_493);
lean_dec(x_460);
x_494 = lean_box(0);
x_495 = x_500;
goto block_499;
}
block_499:
{
lean_object* x_496; 
if (x_495 == 0)
{
x_496 = x_494;
goto block_497;
}
else
{
lean_object* x_498; 
x_498 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_498, 0, x_493);
x_496 = x_498;
goto block_497;
}
block_497:
{
return x_496;
}
}
}
}
block_637:
{
lean_object* x_507; 
lean_inc(x_505);
lean_inc_ref(x_504);
lean_inc(x_503);
lean_inc_ref(x_502);
lean_inc_ref(x_157);
x_507 = l_refutableHasNotBit_x3f(x_157, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
lean_dec_ref(x_507);
if (lean_obj_tag(x_508) == 1)
{
lean_object* x_509; lean_object* x_510; uint8_t x_511; uint8_t x_548; 
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_509 = lean_ctor_get(x_508, 0);
x_548 = !lean_is_exclusive(x_508);
if (x_548 == 0)
{
x_510 = x_508;
x_511 = x_548;
goto block_547;
}
else
{
lean_inc(x_509);
lean_dec(x_508);
x_510 = lean_box(0);
x_511 = x_548;
goto block_547;
}
block_547:
{
lean_object* x_512; 
lean_inc(x_2);
x_512 = l_Lean_MVarId_getType(x_2, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
lean_dec_ref(x_512);
x_514 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_503);
x_515 = l_Lean_Meta_mkAbsurd(x_513, x_509, x_514, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
lean_dec_ref(x_515);
x_517 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_516, x_503);
lean_dec(x_503);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; 
lean_dec_ref(x_517);
x_518 = lean_box(x_12);
if (x_511 == 0)
{
lean_ctor_set(x_510, 0, x_518);
x_519 = x_510;
goto block_521;
}
else
{
lean_object* x_522; 
x_522 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_522, 0, x_518);
x_519 = x_522;
goto block_521;
}
block_521:
{
lean_object* x_520; 
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_37);
x_17 = x_520;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_523; lean_object* x_524; uint8_t x_525; uint8_t x_530; 
lean_del_object(x_510);
lean_del_object(x_15);
lean_dec(x_14);
x_523 = lean_ctor_get(x_517, 0);
x_530 = !lean_is_exclusive(x_517);
if (x_530 == 0)
{
x_524 = x_517;
x_525 = x_530;
goto block_529;
}
else
{
lean_inc(x_523);
lean_dec(x_517);
x_524 = lean_box(0);
x_525 = x_530;
goto block_529;
}
block_529:
{
lean_object* x_526; 
if (x_525 == 0)
{
x_526 = x_524;
goto block_527;
}
else
{
lean_object* x_528; 
x_528 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_528, 0, x_523);
x_526 = x_528;
goto block_527;
}
block_527:
{
return x_526;
}
}
}
}
else
{
lean_object* x_531; lean_object* x_532; uint8_t x_533; uint8_t x_538; 
lean_del_object(x_510);
lean_dec(x_503);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_531 = lean_ctor_get(x_515, 0);
x_538 = !lean_is_exclusive(x_515);
if (x_538 == 0)
{
x_532 = x_515;
x_533 = x_538;
goto block_537;
}
else
{
lean_inc(x_531);
lean_dec(x_515);
x_532 = lean_box(0);
x_533 = x_538;
goto block_537;
}
block_537:
{
lean_object* x_534; 
if (x_533 == 0)
{
x_534 = x_532;
goto block_535;
}
else
{
lean_object* x_536; 
x_536 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_536, 0, x_531);
x_534 = x_536;
goto block_535;
}
block_535:
{
return x_534;
}
}
}
}
else
{
lean_object* x_539; lean_object* x_540; uint8_t x_541; uint8_t x_546; 
lean_del_object(x_510);
lean_dec(x_509);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_539 = lean_ctor_get(x_512, 0);
x_546 = !lean_is_exclusive(x_512);
if (x_546 == 0)
{
x_540 = x_512;
x_541 = x_546;
goto block_545;
}
else
{
lean_inc(x_539);
lean_dec(x_512);
x_540 = lean_box(0);
x_541 = x_546;
goto block_545;
}
block_545:
{
lean_object* x_542; 
if (x_541 == 0)
{
x_542 = x_540;
goto block_543;
}
else
{
lean_object* x_544; 
x_544 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_544, 0, x_539);
x_542 = x_544;
goto block_543;
}
block_543:
{
return x_542;
}
}
}
}
}
else
{
lean_object* x_549; 
lean_dec(x_508);
lean_inc(x_505);
lean_inc_ref(x_504);
lean_inc(x_503);
lean_inc_ref(x_502);
lean_inc_ref(x_157);
x_549 = l_Lean_Meta_matchNe_x3f(x_157, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
lean_dec_ref(x_549);
if (lean_obj_tag(x_550) == 1)
{
lean_object* x_551; lean_object* x_552; uint8_t x_553; uint8_t x_620; 
x_551 = lean_ctor_get(x_550, 0);
x_620 = !lean_is_exclusive(x_550);
if (x_620 == 0)
{
x_552 = x_550;
x_553 = x_620;
goto block_619;
}
else
{
lean_inc(x_551);
lean_dec(x_550);
x_552 = lean_box(0);
x_553 = x_620;
goto block_619;
}
block_619:
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint8_t x_558; uint8_t x_618; 
x_554 = lean_ctor_get(x_551, 1);
lean_inc(x_554);
lean_dec(x_551);
x_555 = lean_ctor_get(x_554, 0);
x_556 = lean_ctor_get(x_554, 1);
x_618 = !lean_is_exclusive(x_554);
if (x_618 == 0)
{
x_557 = x_554;
x_558 = x_618;
goto block_617;
}
else
{
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_554);
x_557 = lean_box(0);
x_558 = x_618;
goto block_617;
}
block_617:
{
lean_object* x_559; 
lean_inc(x_505);
lean_inc_ref(x_504);
lean_inc(x_503);
lean_inc_ref(x_502);
lean_inc(x_555);
x_559 = l_Lean_Meta_isExprDefEq(x_555, x_556, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; uint8_t x_561; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
lean_dec_ref(x_559);
x_561 = lean_unbox(x_560);
lean_dec(x_560);
if (x_561 == 0)
{
lean_del_object(x_557);
lean_dec(x_555);
lean_del_object(x_552);
x_455 = x_502;
x_456 = x_503;
x_457 = x_504;
x_458 = x_505;
x_459 = lean_box(0);
goto block_501;
}
else
{
lean_object* x_562; 
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_562 = l_Lean_MVarId_getType(x_2, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
lean_dec_ref(x_562);
lean_inc(x_505);
lean_inc_ref(x_504);
lean_inc(x_503);
lean_inc_ref(x_502);
x_564 = l_Lean_Meta_mkEqRefl(x_555, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
lean_dec_ref(x_564);
x_566 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_503);
x_567 = l_Lean_Meta_mkAbsurd(x_563, x_565, x_566, x_502, x_503, x_504, x_505);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
lean_dec_ref(x_567);
x_569 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_568, x_503);
lean_dec(x_503);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; 
lean_dec_ref(x_569);
x_570 = lean_box(x_12);
if (x_553 == 0)
{
lean_ctor_set(x_552, 0, x_570);
x_571 = x_552;
goto block_575;
}
else
{
lean_object* x_576; 
x_576 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_576, 0, x_570);
x_571 = x_576;
goto block_575;
}
block_575:
{
lean_object* x_572; 
if (x_558 == 0)
{
lean_ctor_set(x_557, 1, x_37);
lean_ctor_set(x_557, 0, x_571);
x_572 = x_557;
goto block_573;
}
else
{
lean_object* x_574; 
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_571);
lean_ctor_set(x_574, 1, x_37);
x_572 = x_574;
goto block_573;
}
block_573:
{
x_17 = x_572;
x_18 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_577; lean_object* x_578; uint8_t x_579; uint8_t x_584; 
lean_del_object(x_557);
lean_del_object(x_552);
lean_del_object(x_15);
lean_dec(x_14);
x_577 = lean_ctor_get(x_569, 0);
x_584 = !lean_is_exclusive(x_569);
if (x_584 == 0)
{
x_578 = x_569;
x_579 = x_584;
goto block_583;
}
else
{
lean_inc(x_577);
lean_dec(x_569);
x_578 = lean_box(0);
x_579 = x_584;
goto block_583;
}
block_583:
{
lean_object* x_580; 
if (x_579 == 0)
{
x_580 = x_578;
goto block_581;
}
else
{
lean_object* x_582; 
x_582 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_582, 0, x_577);
x_580 = x_582;
goto block_581;
}
block_581:
{
return x_580;
}
}
}
}
else
{
lean_object* x_585; lean_object* x_586; uint8_t x_587; uint8_t x_592; 
lean_del_object(x_557);
lean_del_object(x_552);
lean_dec(x_503);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_585 = lean_ctor_get(x_567, 0);
x_592 = !lean_is_exclusive(x_567);
if (x_592 == 0)
{
x_586 = x_567;
x_587 = x_592;
goto block_591;
}
else
{
lean_inc(x_585);
lean_dec(x_567);
x_586 = lean_box(0);
x_587 = x_592;
goto block_591;
}
block_591:
{
lean_object* x_588; 
if (x_587 == 0)
{
x_588 = x_586;
goto block_589;
}
else
{
lean_object* x_590; 
x_590 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_590, 0, x_585);
x_588 = x_590;
goto block_589;
}
block_589:
{
return x_588;
}
}
}
}
else
{
lean_object* x_593; lean_object* x_594; uint8_t x_595; uint8_t x_600; 
lean_dec(x_563);
lean_del_object(x_557);
lean_del_object(x_552);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_593 = lean_ctor_get(x_564, 0);
x_600 = !lean_is_exclusive(x_564);
if (x_600 == 0)
{
x_594 = x_564;
x_595 = x_600;
goto block_599;
}
else
{
lean_inc(x_593);
lean_dec(x_564);
x_594 = lean_box(0);
x_595 = x_600;
goto block_599;
}
block_599:
{
lean_object* x_596; 
if (x_595 == 0)
{
x_596 = x_594;
goto block_597;
}
else
{
lean_object* x_598; 
x_598 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_598, 0, x_593);
x_596 = x_598;
goto block_597;
}
block_597:
{
return x_596;
}
}
}
}
else
{
lean_object* x_601; lean_object* x_602; uint8_t x_603; uint8_t x_608; 
lean_del_object(x_557);
lean_dec(x_555);
lean_del_object(x_552);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_601 = lean_ctor_get(x_562, 0);
x_608 = !lean_is_exclusive(x_562);
if (x_608 == 0)
{
x_602 = x_562;
x_603 = x_608;
goto block_607;
}
else
{
lean_inc(x_601);
lean_dec(x_562);
x_602 = lean_box(0);
x_603 = x_608;
goto block_607;
}
block_607:
{
lean_object* x_604; 
if (x_603 == 0)
{
x_604 = x_602;
goto block_605;
}
else
{
lean_object* x_606; 
x_606 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_606, 0, x_601);
x_604 = x_606;
goto block_605;
}
block_605:
{
return x_604;
}
}
}
}
}
else
{
lean_object* x_609; lean_object* x_610; uint8_t x_611; uint8_t x_616; 
lean_del_object(x_557);
lean_dec(x_555);
lean_del_object(x_552);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_609 = lean_ctor_get(x_559, 0);
x_616 = !lean_is_exclusive(x_559);
if (x_616 == 0)
{
x_610 = x_559;
x_611 = x_616;
goto block_615;
}
else
{
lean_inc(x_609);
lean_dec(x_559);
x_610 = lean_box(0);
x_611 = x_616;
goto block_615;
}
block_615:
{
lean_object* x_612; 
if (x_611 == 0)
{
x_612 = x_610;
goto block_613;
}
else
{
lean_object* x_614; 
x_614 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_614, 0, x_609);
x_612 = x_614;
goto block_613;
}
block_613:
{
return x_612;
}
}
}
}
}
}
else
{
lean_dec(x_550);
x_455 = x_502;
x_456 = x_503;
x_457 = x_504;
x_458 = x_505;
x_459 = lean_box(0);
goto block_501;
}
}
else
{
lean_object* x_621; lean_object* x_622; uint8_t x_623; uint8_t x_628; 
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_621 = lean_ctor_get(x_549, 0);
x_628 = !lean_is_exclusive(x_549);
if (x_628 == 0)
{
x_622 = x_549;
x_623 = x_628;
goto block_627;
}
else
{
lean_inc(x_621);
lean_dec(x_549);
x_622 = lean_box(0);
x_623 = x_628;
goto block_627;
}
block_627:
{
lean_object* x_624; 
if (x_623 == 0)
{
x_624 = x_622;
goto block_625;
}
else
{
lean_object* x_626; 
x_626 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_626, 0, x_621);
x_624 = x_626;
goto block_625;
}
block_625:
{
return x_624;
}
}
}
}
}
else
{
lean_object* x_629; lean_object* x_630; uint8_t x_631; uint8_t x_636; 
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec_ref(x_157);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_629 = lean_ctor_get(x_507, 0);
x_636 = !lean_is_exclusive(x_507);
if (x_636 == 0)
{
x_630 = x_507;
x_631 = x_636;
goto block_635;
}
else
{
lean_inc(x_629);
lean_dec(x_507);
x_630 = lean_box(0);
x_631 = x_636;
goto block_635;
}
block_635:
{
lean_object* x_632; 
if (x_631 == 0)
{
x_632 = x_630;
goto block_633;
}
else
{
lean_object* x_634; 
x_634 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_634, 0, x_629);
x_632 = x_634;
goto block_633;
}
block_633:
{
return x_632;
}
}
}
}
}
else
{
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_79;
x_27 = lean_box(0);
goto block_32;
}
block_78:
{
lean_object* x_43; 
lean_inc(x_2);
x_43 = l_Lean_MVarId_getType(x_2, x_38, x_41, x_40, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_41);
x_46 = l_Lean_Meta_mkNoConfusion(x_44, x_45, x_38, x_41, x_40, x_42);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_47, x_41);
lean_dec(x_41);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_48);
x_49 = lean_box(x_12);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_49);
x_50 = x_35;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_49);
x_50 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_37);
x_17 = x_51;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_del_object(x_35);
lean_del_object(x_15);
lean_dec(x_14);
x_54 = lean_ctor_get(x_48, 0);
x_61 = !lean_is_exclusive(x_48);
if (x_61 == 0)
{
x_55 = x_48;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec(x_41);
lean_del_object(x_35);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_62 = lean_ctor_get(x_46, 0);
x_69 = !lean_is_exclusive(x_46);
if (x_69 == 0)
{
x_63 = x_46;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_46);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_38);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_70 = lean_ctor_get(x_43, 0);
x_77 = !lean_is_exclusive(x_43);
if (x_77 == 0)
{
x_71 = x_43;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_43);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_70);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
block_101:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_1, 0);
x_86 = l_Lean_LocalDecl_fvarId(x_34);
lean_dec(x_34);
lean_inc(x_85);
lean_inc(x_2);
x_87 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_2, x_86, x_85, x_81, x_83, x_80, x_82);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_79;
x_27 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_90 = lean_box(x_12);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_37);
x_17 = x_92;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_100; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_93 = lean_ctor_get(x_87, 0);
x_100 = !lean_is_exclusive(x_87);
if (x_100 == 0)
{
x_94 = x_87;
x_95 = x_100;
goto block_99;
}
else
{
lean_inc(x_93);
lean_dec(x_87);
x_94 = lean_box(0);
x_95 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_96; 
if (x_95 == 0)
{
x_96 = x_94;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_93);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
block_108:
{
if (x_107 == 0)
{
lean_dec(x_105);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec_ref(x_102);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_79;
x_27 = lean_box(0);
goto block_32;
}
else
{
x_80 = x_102;
x_81 = x_103;
x_82 = x_104;
x_83 = x_105;
x_84 = lean_box(0);
goto block_101;
}
}
block_116:
{
if (x_111 == 0)
{
x_80 = x_110;
x_81 = x_112;
x_82 = x_113;
x_83 = x_114;
x_84 = lean_box(0);
goto block_101;
}
else
{
x_102 = x_110;
x_103 = x_112;
x_104 = x_113;
x_105 = x_114;
x_106 = lean_box(0);
x_107 = x_109;
goto block_108;
}
}
block_124:
{
if (x_123 == 0)
{
x_102 = x_117;
x_103 = x_119;
x_104 = x_120;
x_105 = x_121;
x_106 = lean_box(0);
x_107 = x_109;
goto block_108;
}
else
{
x_110 = x_117;
x_111 = x_118;
x_112 = x_119;
x_113 = x_120;
x_114 = x_121;
x_115 = lean_box(0);
goto block_116;
}
}
block_133:
{
uint8_t x_132; 
x_132 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_132 == 0)
{
x_117 = x_129;
x_118 = x_125;
x_119 = x_127;
x_120 = x_130;
x_121 = x_128;
x_122 = lean_box(0);
x_123 = x_109;
goto block_124;
}
else
{
if (x_126 == 0)
{
x_110 = x_129;
x_111 = x_125;
x_112 = x_127;
x_113 = x_130;
x_114 = x_128;
x_115 = lean_box(0);
goto block_116;
}
else
{
x_117 = x_129;
x_118 = x_125;
x_119 = x_127;
x_120 = x_130;
x_121 = x_128;
x_122 = lean_box(0);
x_123 = x_109;
goto block_124;
}
}
}
block_156:
{
if (x_141 == 0)
{
x_125 = x_135;
x_126 = x_136;
x_127 = x_134;
x_128 = x_137;
x_129 = x_139;
x_130 = x_140;
x_131 = lean_box(0);
goto block_133;
}
else
{
lean_object* x_142; 
lean_inc(x_140);
lean_inc_ref(x_139);
lean_inc(x_137);
lean_inc_ref(x_134);
lean_inc(x_34);
lean_inc(x_2);
x_142 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_2, x_34, x_134, x_137, x_139, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
x_125 = x_135;
x_126 = x_136;
x_127 = x_134;
x_128 = x_137;
x_129 = x_139;
x_130 = x_140;
x_131 = lean_box(0);
goto block_133;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_140);
lean_dec_ref(x_139);
lean_dec(x_137);
lean_dec_ref(x_134);
lean_dec(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_145 = lean_box(x_12);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_37);
x_17 = x_147;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_155; 
lean_dec(x_140);
lean_dec_ref(x_139);
lean_dec(x_137);
lean_dec_ref(x_134);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_148 = lean_ctor_get(x_142, 0);
x_155 = !lean_is_exclusive(x_142);
if (x_155 == 0)
{
x_149 = x_142;
x_150 = x_155;
goto block_154;
}
else
{
lean_inc(x_148);
lean_dec(x_142);
x_149 = lean_box(0);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_150 == 0)
{
x_151 = x_149;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_148);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
}
}
}
block_24:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_14);
x_20 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
block_32:
{
lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
x_29 = 1;
x_30 = lean_usize_add(x_5, x_29);
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_4, x_30, x_28, x_7, x_8, x_9, x_10);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_724; 
x_14 = lean_ctor_get(x_6, 1);
x_724 = !lean_is_exclusive(x_6);
if (x_724 == 0)
{
lean_object* x_725; 
x_725 = lean_ctor_get(x_6, 0);
lean_dec(x_725);
x_15 = x_6;
x_16 = x_724;
goto block_723;
}
else
{
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_724;
goto block_723;
}
block_723:
{
lean_object* x_17; lean_object* x_18; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_33; 
x_25 = lean_box(0);
x_33 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_33) == 0)
{
lean_del_object(x_15);
x_26 = x_14;
x_27 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_722; 
x_34 = lean_ctor_get(x_33, 0);
x_722 = !lean_is_exclusive(x_33);
if (x_722 == 0)
{
x_35 = x_33;
x_36 = x_722;
goto block_721;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_722;
goto block_721;
}
block_721:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_37 = lean_box(0);
x_80 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
x_111 = l_Lean_LocalDecl_isImplementationDetail(x_34);
if (x_111 == 0)
{
lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_171; uint8_t x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_182; uint8_t x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_193; uint8_t x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_292; uint8_t x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_301; uint8_t x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_312; uint8_t x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; lean_object* x_332; uint8_t x_333; uint8_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; uint8_t x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_651; 
x_160 = l_Lean_LocalDecl_type(x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_160);
x_651 = l_Lean_Meta_matchNot_x3f(x_160, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
lean_dec_ref(x_651);
if (lean_obj_tag(x_652) == 1)
{
lean_object* x_653; lean_object* x_654; uint8_t x_655; uint8_t x_712; 
x_653 = lean_ctor_get(x_652, 0);
x_712 = !lean_is_exclusive(x_652);
if (x_712 == 0)
{
x_654 = x_652;
x_655 = x_712;
goto block_711;
}
else
{
lean_inc(x_653);
lean_dec(x_652);
x_654 = lean_box(0);
x_655 = x_712;
goto block_711;
}
block_711:
{
lean_object* x_656; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_656 = l_Lean_Meta_findLocalDeclWithType_x3f(x_653, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
lean_dec_ref(x_656);
if (lean_obj_tag(x_657) == 1)
{
lean_object* x_658; lean_object* x_659; uint8_t x_660; uint8_t x_702; 
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec_ref(x_1);
x_658 = lean_ctor_get(x_657, 0);
x_702 = !lean_is_exclusive(x_657);
if (x_702 == 0)
{
x_659 = x_657;
x_660 = x_702;
goto block_701;
}
else
{
lean_inc(x_658);
lean_dec(x_657);
x_659 = lean_box(0);
x_660 = x_702;
goto block_701;
}
block_701:
{
lean_object* x_661; 
lean_inc(x_2);
x_661 = l_Lean_MVarId_getType(x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
lean_dec_ref(x_661);
x_663 = l_Lean_LocalDecl_toExpr(x_34);
x_664 = l_Lean_mkFVar(x_658);
x_665 = l_Lean_Expr_app___override(x_663, x_664);
lean_inc(x_8);
x_666 = l_Lean_Meta_mkFalseElim(x_662, x_665, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
lean_dec_ref(x_666);
x_668 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_667, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; 
lean_dec_ref(x_668);
x_669 = lean_box(x_12);
if (x_660 == 0)
{
lean_ctor_set(x_659, 0, x_669);
x_670 = x_659;
goto block_675;
}
else
{
lean_object* x_676; 
x_676 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_676, 0, x_669);
x_670 = x_676;
goto block_675;
}
block_675:
{
lean_object* x_671; lean_object* x_672; 
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_37);
if (x_655 == 0)
{
lean_ctor_set_tag(x_654, 0);
lean_ctor_set(x_654, 0, x_671);
x_672 = x_654;
goto block_673;
}
else
{
lean_object* x_674; 
x_674 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_674, 0, x_671);
x_672 = x_674;
goto block_673;
}
block_673:
{
x_17 = x_672;
x_18 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_677; lean_object* x_678; uint8_t x_679; uint8_t x_684; 
lean_del_object(x_659);
lean_del_object(x_654);
lean_del_object(x_15);
lean_dec(x_14);
x_677 = lean_ctor_get(x_668, 0);
x_684 = !lean_is_exclusive(x_668);
if (x_684 == 0)
{
x_678 = x_668;
x_679 = x_684;
goto block_683;
}
else
{
lean_inc(x_677);
lean_dec(x_668);
x_678 = lean_box(0);
x_679 = x_684;
goto block_683;
}
block_683:
{
lean_object* x_680; 
if (x_679 == 0)
{
x_680 = x_678;
goto block_681;
}
else
{
lean_object* x_682; 
x_682 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_682, 0, x_677);
x_680 = x_682;
goto block_681;
}
block_681:
{
return x_680;
}
}
}
}
else
{
lean_object* x_685; lean_object* x_686; uint8_t x_687; uint8_t x_692; 
lean_del_object(x_659);
lean_del_object(x_654);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
x_685 = lean_ctor_get(x_666, 0);
x_692 = !lean_is_exclusive(x_666);
if (x_692 == 0)
{
x_686 = x_666;
x_687 = x_692;
goto block_691;
}
else
{
lean_inc(x_685);
lean_dec(x_666);
x_686 = lean_box(0);
x_687 = x_692;
goto block_691;
}
block_691:
{
lean_object* x_688; 
if (x_687 == 0)
{
x_688 = x_686;
goto block_689;
}
else
{
lean_object* x_690; 
x_690 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_690, 0, x_685);
x_688 = x_690;
goto block_689;
}
block_689:
{
return x_688;
}
}
}
}
else
{
lean_object* x_693; lean_object* x_694; uint8_t x_695; uint8_t x_700; 
lean_del_object(x_659);
lean_dec(x_658);
lean_del_object(x_654);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_693 = lean_ctor_get(x_661, 0);
x_700 = !lean_is_exclusive(x_661);
if (x_700 == 0)
{
x_694 = x_661;
x_695 = x_700;
goto block_699;
}
else
{
lean_inc(x_693);
lean_dec(x_661);
x_694 = lean_box(0);
x_695 = x_700;
goto block_699;
}
block_699:
{
lean_object* x_696; 
if (x_695 == 0)
{
x_696 = x_694;
goto block_697;
}
else
{
lean_object* x_698; 
x_698 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_698, 0, x_693);
x_696 = x_698;
goto block_697;
}
block_697:
{
return x_696;
}
}
}
}
}
else
{
lean_dec(x_657);
lean_del_object(x_654);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_513 = x_7;
x_514 = x_8;
x_515 = x_9;
x_516 = x_10;
x_517 = lean_box(0);
goto block_650;
}
}
else
{
lean_object* x_703; lean_object* x_704; uint8_t x_705; uint8_t x_710; 
lean_del_object(x_654);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_703 = lean_ctor_get(x_656, 0);
x_710 = !lean_is_exclusive(x_656);
if (x_710 == 0)
{
x_704 = x_656;
x_705 = x_710;
goto block_709;
}
else
{
lean_inc(x_703);
lean_dec(x_656);
x_704 = lean_box(0);
x_705 = x_710;
goto block_709;
}
block_709:
{
lean_object* x_706; 
if (x_705 == 0)
{
x_706 = x_704;
goto block_707;
}
else
{
lean_object* x_708; 
x_708 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_708, 0, x_703);
x_706 = x_708;
goto block_707;
}
block_707:
{
return x_706;
}
}
}
}
}
else
{
lean_dec(x_652);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_513 = x_7;
x_514 = x_8;
x_515 = x_9;
x_516 = x_10;
x_517 = lean_box(0);
goto block_650;
}
}
else
{
lean_object* x_713; lean_object* x_714; uint8_t x_715; uint8_t x_720; 
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_713 = lean_ctor_get(x_651, 0);
x_720 = !lean_is_exclusive(x_651);
if (x_720 == 0)
{
x_714 = x_651;
x_715 = x_720;
goto block_719;
}
else
{
lean_inc(x_713);
lean_dec(x_651);
x_714 = lean_box(0);
x_715 = x_720;
goto block_719;
}
block_719:
{
lean_object* x_716; 
if (x_715 == 0)
{
x_716 = x_714;
goto block_717;
}
else
{
lean_object* x_718; 
x_718 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_718, 0, x_713);
x_716 = x_718;
goto block_717;
}
block_717:
{
return x_716;
}
}
}
block_170:
{
uint8_t x_168; 
x_168 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_168 == 0)
{
lean_dec_ref(x_160);
x_136 = x_162;
x_137 = x_161;
x_138 = x_166;
x_139 = x_163;
x_140 = x_165;
x_141 = x_164;
x_142 = lean_box(0);
x_143 = x_111;
goto block_159;
}
else
{
uint8_t x_169; 
x_169 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_160);
x_136 = x_162;
x_137 = x_161;
x_138 = x_166;
x_139 = x_163;
x_140 = x_165;
x_141 = x_164;
x_142 = lean_box(0);
x_143 = x_169;
goto block_159;
}
}
block_181:
{
if (x_179 == 0)
{
lean_dec_ref(x_175);
x_161 = x_173;
x_162 = x_172;
x_163 = x_177;
x_164 = x_178;
x_165 = x_174;
x_166 = x_171;
x_167 = lean_box(0);
goto block_170;
}
else
{
lean_object* x_180; 
lean_dec(x_178);
lean_dec_ref(x_177);
lean_dec_ref(x_174);
lean_dec(x_171);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_175);
return x_180;
}
}
block_192:
{
uint8_t x_190; 
x_190 = l_Lean_Exception_isInterrupt(x_188);
if (x_190 == 0)
{
uint8_t x_191; 
lean_inc_ref(x_188);
x_191 = l_Lean_Exception_isRuntime(x_188);
x_171 = x_182;
x_172 = x_184;
x_173 = x_183;
x_174 = x_185;
x_175 = x_188;
x_176 = lean_box(0);
x_177 = x_186;
x_178 = x_187;
x_179 = x_191;
goto block_181;
}
else
{
x_171 = x_182;
x_172 = x_184;
x_173 = x_183;
x_174 = x_185;
x_175 = x_188;
x_176 = lean_box(0);
x_177 = x_186;
x_178 = x_187;
x_179 = x_190;
goto block_181;
}
}
block_291:
{
lean_object* x_200; 
lean_inc(x_193);
lean_inc_ref(x_196);
lean_inc(x_199);
lean_inc_ref(x_198);
lean_inc_ref(x_160);
x_200 = l_Lean_Meta_mkDecide(x_160, x_198, x_199, x_196, x_193);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; uint8_t x_289; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec_ref(x_200);
x_202 = l_Lean_Meta_Context_config(x_198);
x_203 = lean_ctor_get_uint8(x_202, 0);
x_204 = lean_ctor_get_uint8(x_202, 1);
x_205 = lean_ctor_get_uint8(x_202, 2);
x_206 = lean_ctor_get_uint8(x_202, 3);
x_207 = lean_ctor_get_uint8(x_202, 4);
x_208 = lean_ctor_get_uint8(x_202, 5);
x_209 = lean_ctor_get_uint8(x_202, 6);
x_210 = lean_ctor_get_uint8(x_202, 7);
x_211 = lean_ctor_get_uint8(x_202, 8);
x_212 = lean_ctor_get_uint8(x_202, 10);
x_213 = lean_ctor_get_uint8(x_202, 11);
x_214 = lean_ctor_get_uint8(x_202, 12);
x_215 = lean_ctor_get_uint8(x_202, 13);
x_216 = lean_ctor_get_uint8(x_202, 14);
x_217 = lean_ctor_get_uint8(x_202, 15);
x_218 = lean_ctor_get_uint8(x_202, 16);
x_219 = lean_ctor_get_uint8(x_202, 17);
x_220 = lean_ctor_get_uint8(x_202, 18);
x_289 = !lean_is_exclusive(x_202);
if (x_289 == 0)
{
x_221 = x_202;
x_222 = x_289;
goto block_288;
}
else
{
lean_dec(x_202);
x_221 = lean_box(0);
x_222 = x_289;
goto block_288;
}
block_288:
{
uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; lean_object* x_234; 
x_223 = lean_ctor_get_uint8(x_198, sizeof(void*)*7);
x_224 = lean_ctor_get(x_198, 1);
x_225 = lean_ctor_get(x_198, 2);
x_226 = lean_ctor_get(x_198, 3);
x_227 = lean_ctor_get(x_198, 4);
x_228 = lean_ctor_get(x_198, 5);
x_229 = lean_ctor_get(x_198, 6);
x_230 = lean_ctor_get_uint8(x_198, sizeof(void*)*7 + 1);
x_231 = lean_ctor_get_uint8(x_198, sizeof(void*)*7 + 2);
x_232 = lean_ctor_get_uint8(x_198, sizeof(void*)*7 + 3);
x_233 = 1;
if (x_222 == 0)
{
x_234 = x_221;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_287, 0, x_203);
lean_ctor_set_uint8(x_287, 1, x_204);
lean_ctor_set_uint8(x_287, 2, x_205);
lean_ctor_set_uint8(x_287, 3, x_206);
lean_ctor_set_uint8(x_287, 4, x_207);
lean_ctor_set_uint8(x_287, 5, x_208);
lean_ctor_set_uint8(x_287, 6, x_209);
lean_ctor_set_uint8(x_287, 7, x_210);
lean_ctor_set_uint8(x_287, 8, x_211);
lean_ctor_set_uint8(x_287, 10, x_212);
lean_ctor_set_uint8(x_287, 11, x_213);
lean_ctor_set_uint8(x_287, 12, x_214);
lean_ctor_set_uint8(x_287, 13, x_215);
lean_ctor_set_uint8(x_287, 14, x_216);
lean_ctor_set_uint8(x_287, 15, x_217);
lean_ctor_set_uint8(x_287, 16, x_218);
lean_ctor_set_uint8(x_287, 17, x_219);
lean_ctor_set_uint8(x_287, 18, x_220);
x_234 = x_287;
goto block_286;
}
block_286:
{
uint64_t x_235; uint64_t x_236; uint64_t x_237; uint64_t x_238; uint64_t x_239; uint64_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_ctor_set_uint8(x_234, 9, x_233);
x_235 = l_Lean_Meta_Context_configKey(x_198);
x_236 = 2;
x_237 = lean_uint64_shift_right(x_235, x_236);
x_238 = lean_uint64_shift_left(x_237, x_236);
x_239 = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
x_240 = lean_uint64_lor(x_238, x_239);
x_241 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_241, 0, x_234);
lean_ctor_set_uint64(x_241, sizeof(void*)*1, x_240);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc_ref(x_226);
lean_inc_ref(x_225);
lean_inc(x_224);
x_242 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_224);
lean_ctor_set(x_242, 2, x_225);
lean_ctor_set(x_242, 3, x_226);
lean_ctor_set(x_242, 4, x_227);
lean_ctor_set(x_242, 5, x_228);
lean_ctor_set(x_242, 6, x_229);
lean_ctor_set_uint8(x_242, sizeof(void*)*7, x_223);
lean_ctor_set_uint8(x_242, sizeof(void*)*7 + 1, x_230);
lean_ctor_set_uint8(x_242, sizeof(void*)*7 + 2, x_231);
lean_ctor_set_uint8(x_242, sizeof(void*)*7 + 3, x_232);
lean_inc(x_193);
lean_inc_ref(x_196);
lean_inc(x_199);
lean_inc(x_201);
x_243 = lean_whnf(x_201, x_242, x_199, x_196, x_193);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
x_246 = l_Lean_Expr_isConstOf(x_244, x_245);
lean_dec(x_244);
if (x_246 == 0)
{
lean_dec(x_201);
x_161 = x_195;
x_162 = x_194;
x_163 = x_198;
x_164 = x_199;
x_165 = x_196;
x_166 = x_193;
x_167 = lean_box(0);
goto block_170;
}
else
{
lean_object* x_247; 
lean_inc(x_193);
lean_inc_ref(x_196);
lean_inc(x_199);
lean_inc_ref(x_198);
lean_inc(x_201);
x_247 = l_Lean_Meta_mkEqRefl(x_201, x_198, x_199, x_196, x_193);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_dec_ref(x_247);
lean_inc(x_2);
x_249 = l_Lean_MVarId_getType(x_2, x_198, x_199, x_196, x_193);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = l_Lean_Expr_getAppNumArgs(x_201);
x_252 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
x_253 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(x_251);
x_254 = lean_mk_array(x_251, x_253);
x_255 = lean_unsigned_to_nat(1u);
x_256 = lean_nat_sub(x_251, x_255);
lean_dec(x_251);
x_257 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_201, x_254, x_256);
x_258 = lean_array_push(x_257, x_248);
x_259 = l_Lean_mkAppN(x_252, x_258);
lean_dec_ref(x_258);
lean_inc(x_34);
x_260 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_193);
lean_inc_ref(x_196);
lean_inc(x_199);
lean_inc_ref(x_198);
x_261 = l_Lean_Meta_mkAbsurd(x_250, x_260, x_259, x_198, x_199, x_196, x_193);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_281; 
x_262 = lean_ctor_get(x_261, 0);
x_281 = !lean_is_exclusive(x_261);
if (x_281 == 0)
{
x_263 = x_261;
x_264 = x_281;
goto block_280;
}
else
{
lean_inc(x_262);
lean_dec(x_261);
x_263 = lean_box(0);
x_264 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_265; 
lean_inc(x_2);
x_265 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_262, x_199);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; uint8_t x_267; uint8_t x_277; 
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_196);
lean_dec(x_193);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_277 = !lean_is_exclusive(x_265);
if (x_277 == 0)
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_265, 0);
lean_dec(x_278);
x_266 = x_265;
x_267 = x_277;
goto block_276;
}
else
{
lean_dec(x_265);
x_266 = lean_box(0);
x_267 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_box(x_12);
if (x_267 == 0)
{
lean_ctor_set_tag(x_266, 1);
lean_ctor_set(x_266, 0, x_268);
x_269 = x_266;
goto block_274;
}
else
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_268);
x_269 = x_275;
goto block_274;
}
block_274:
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_37);
if (x_264 == 0)
{
lean_ctor_set(x_263, 0, x_270);
x_271 = x_263;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_270);
x_271 = x_273;
goto block_272;
}
block_272:
{
x_17 = x_271;
x_18 = lean_box(0);
goto block_24;
}
}
}
}
else
{
lean_object* x_279; 
lean_del_object(x_263);
x_279 = lean_ctor_get(x_265, 0);
lean_inc(x_279);
lean_dec_ref(x_265);
x_182 = x_193;
x_183 = x_195;
x_184 = x_194;
x_185 = x_196;
x_186 = x_198;
x_187 = x_199;
x_188 = x_279;
x_189 = lean_box(0);
goto block_192;
}
}
}
else
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_261, 0);
lean_inc(x_282);
lean_dec_ref(x_261);
x_182 = x_193;
x_183 = x_195;
x_184 = x_194;
x_185 = x_196;
x_186 = x_198;
x_187 = x_199;
x_188 = x_282;
x_189 = lean_box(0);
goto block_192;
}
}
else
{
lean_object* x_283; 
lean_dec(x_248);
lean_dec(x_201);
x_283 = lean_ctor_get(x_249, 0);
lean_inc(x_283);
lean_dec_ref(x_249);
x_182 = x_193;
x_183 = x_195;
x_184 = x_194;
x_185 = x_196;
x_186 = x_198;
x_187 = x_199;
x_188 = x_283;
x_189 = lean_box(0);
goto block_192;
}
}
else
{
lean_object* x_284; 
lean_dec(x_201);
x_284 = lean_ctor_get(x_247, 0);
lean_inc(x_284);
lean_dec_ref(x_247);
x_182 = x_193;
x_183 = x_195;
x_184 = x_194;
x_185 = x_196;
x_186 = x_198;
x_187 = x_199;
x_188 = x_284;
x_189 = lean_box(0);
goto block_192;
}
}
}
else
{
lean_object* x_285; 
lean_dec(x_201);
x_285 = lean_ctor_get(x_243, 0);
lean_inc(x_285);
lean_dec_ref(x_243);
x_182 = x_193;
x_183 = x_195;
x_184 = x_194;
x_185 = x_196;
x_186 = x_198;
x_187 = x_199;
x_188 = x_285;
x_189 = lean_box(0);
goto block_192;
}
}
}
}
else
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_200, 0);
lean_inc(x_290);
lean_dec_ref(x_200);
x_182 = x_193;
x_183 = x_195;
x_184 = x_194;
x_185 = x_196;
x_186 = x_198;
x_187 = x_199;
x_188 = x_290;
x_189 = lean_box(0);
goto block_192;
}
}
block_300:
{
if (x_299 == 0)
{
x_161 = x_294;
x_162 = x_293;
x_163 = x_297;
x_164 = x_298;
x_165 = x_295;
x_166 = x_292;
x_167 = lean_box(0);
goto block_170;
}
else
{
x_193 = x_292;
x_194 = x_293;
x_195 = x_294;
x_196 = x_295;
x_197 = lean_box(0);
x_198 = x_297;
x_199 = x_298;
goto block_291;
}
}
block_311:
{
if (x_309 == 0)
{
lean_dec_ref(x_305);
x_292 = x_301;
x_293 = x_303;
x_294 = x_302;
x_295 = x_304;
x_296 = lean_box(0);
x_297 = x_306;
x_298 = x_308;
x_299 = x_111;
goto block_300;
}
else
{
uint8_t x_310; 
x_310 = l_Lean_Expr_hasFVar(x_305);
lean_dec_ref(x_305);
if (x_310 == 0)
{
x_193 = x_301;
x_194 = x_303;
x_195 = x_302;
x_196 = x_304;
x_197 = lean_box(0);
x_198 = x_306;
x_199 = x_308;
goto block_291;
}
else
{
x_292 = x_301;
x_293 = x_303;
x_294 = x_302;
x_295 = x_304;
x_296 = lean_box(0);
x_297 = x_306;
x_298 = x_308;
x_299 = x_111;
goto block_300;
}
}
}
block_331:
{
lean_object* x_320; 
lean_inc_ref(x_160);
x_320 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_160, x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; uint8_t x_322; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
lean_dec_ref(x_320);
x_322 = l_Lean_Expr_hasMVar(x_321);
if (x_322 == 0)
{
x_301 = x_312;
x_302 = x_313;
x_303 = x_314;
x_304 = x_315;
x_305 = x_321;
x_306 = x_316;
x_307 = lean_box(0);
x_308 = x_318;
x_309 = x_319;
goto block_311;
}
else
{
x_301 = x_312;
x_302 = x_313;
x_303 = x_314;
x_304 = x_315;
x_305 = x_321;
x_306 = x_316;
x_307 = lean_box(0);
x_308 = x_318;
x_309 = x_111;
goto block_311;
}
}
else
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; uint8_t x_330; 
lean_dec(x_318);
lean_dec_ref(x_316);
lean_dec_ref(x_315);
lean_dec(x_312);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_323 = lean_ctor_get(x_320, 0);
x_330 = !lean_is_exclusive(x_320);
if (x_330 == 0)
{
x_324 = x_320;
x_325 = x_330;
goto block_329;
}
else
{
lean_inc(x_323);
lean_dec(x_320);
x_324 = lean_box(0);
x_325 = x_330;
goto block_329;
}
block_329:
{
lean_object* x_326; 
if (x_325 == 0)
{
x_326 = x_324;
goto block_327;
}
else
{
lean_object* x_328; 
x_328 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_328, 0, x_323);
x_326 = x_328;
goto block_327;
}
block_327:
{
return x_326;
}
}
}
}
block_340:
{
if (x_339 == 0)
{
x_161 = x_334;
x_162 = x_333;
x_163 = x_336;
x_164 = x_338;
x_165 = x_335;
x_166 = x_332;
x_167 = lean_box(0);
goto block_170;
}
else
{
x_312 = x_332;
x_313 = x_334;
x_314 = x_333;
x_315 = x_335;
x_316 = x_336;
x_317 = lean_box(0);
x_318 = x_338;
x_319 = x_339;
goto block_331;
}
}
block_350:
{
uint8_t x_348; 
x_348 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_348 == 0)
{
x_332 = x_346;
x_333 = x_342;
x_334 = x_341;
x_335 = x_345;
x_336 = x_343;
x_337 = lean_box(0);
x_338 = x_344;
x_339 = x_111;
goto block_340;
}
else
{
uint8_t x_349; 
x_349 = l_Lean_Expr_hasFVar(x_160);
if (x_349 == 0)
{
x_312 = x_346;
x_313 = x_341;
x_314 = x_342;
x_315 = x_345;
x_316 = x_343;
x_317 = lean_box(0);
x_318 = x_344;
x_319 = x_348;
goto block_331;
}
else
{
x_332 = x_346;
x_333 = x_342;
x_334 = x_341;
x_335 = x_345;
x_336 = x_343;
x_337 = lean_box(0);
x_338 = x_344;
x_339 = x_111;
goto block_340;
}
}
}
block_414:
{
lean_object* x_359; 
lean_inc(x_354);
lean_inc_ref(x_351);
lean_inc(x_358);
lean_inc_ref(x_356);
x_359 = l_Lean_Meta_isExprDefEq(x_352, x_355, x_356, x_358, x_351, x_354);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; uint8_t x_361; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
lean_dec_ref(x_359);
x_361 = lean_unbox(x_360);
lean_dec(x_360);
if (x_361 == 0)
{
x_341 = x_353;
x_342 = x_12;
x_343 = x_356;
x_344 = x_358;
x_345 = x_351;
x_346 = x_354;
x_347 = lean_box(0);
goto block_350;
}
else
{
lean_object* x_362; 
lean_dec_ref(x_160);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_362 = l_Lean_MVarId_getType(x_2, x_356, x_358, x_351, x_354);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec_ref(x_362);
x_364 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_354);
lean_inc_ref(x_351);
lean_inc(x_358);
lean_inc_ref(x_356);
x_365 = l_Lean_Meta_mkEqOfHEq(x_364, x_12, x_356, x_358, x_351, x_354);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
lean_dec_ref(x_365);
lean_inc(x_358);
x_367 = l_Lean_Meta_mkNoConfusion(x_363, x_366, x_356, x_358, x_351, x_354);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
lean_dec_ref(x_367);
x_369 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_368, x_358);
lean_dec(x_358);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec_ref(x_369);
x_370 = lean_box(x_12);
x_371 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_371, 0, x_370);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_37);
x_373 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_373, 0, x_372);
x_17 = x_373;
x_18 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; uint8_t x_381; 
lean_del_object(x_15);
lean_dec(x_14);
x_374 = lean_ctor_get(x_369, 0);
x_381 = !lean_is_exclusive(x_369);
if (x_381 == 0)
{
x_375 = x_369;
x_376 = x_381;
goto block_380;
}
else
{
lean_inc(x_374);
lean_dec(x_369);
x_375 = lean_box(0);
x_376 = x_381;
goto block_380;
}
block_380:
{
lean_object* x_377; 
if (x_376 == 0)
{
x_377 = x_375;
goto block_378;
}
else
{
lean_object* x_379; 
x_379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_379, 0, x_374);
x_377 = x_379;
goto block_378;
}
block_378:
{
return x_377;
}
}
}
}
else
{
lean_object* x_382; lean_object* x_383; uint8_t x_384; uint8_t x_389; 
lean_dec(x_358);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_382 = lean_ctor_get(x_367, 0);
x_389 = !lean_is_exclusive(x_367);
if (x_389 == 0)
{
x_383 = x_367;
x_384 = x_389;
goto block_388;
}
else
{
lean_inc(x_382);
lean_dec(x_367);
x_383 = lean_box(0);
x_384 = x_389;
goto block_388;
}
block_388:
{
lean_object* x_385; 
if (x_384 == 0)
{
x_385 = x_383;
goto block_386;
}
else
{
lean_object* x_387; 
x_387 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_387, 0, x_382);
x_385 = x_387;
goto block_386;
}
block_386:
{
return x_385;
}
}
}
}
else
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; uint8_t x_397; 
lean_dec(x_363);
lean_dec(x_358);
lean_dec_ref(x_356);
lean_dec(x_354);
lean_dec_ref(x_351);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_390 = lean_ctor_get(x_365, 0);
x_397 = !lean_is_exclusive(x_365);
if (x_397 == 0)
{
x_391 = x_365;
x_392 = x_397;
goto block_396;
}
else
{
lean_inc(x_390);
lean_dec(x_365);
x_391 = lean_box(0);
x_392 = x_397;
goto block_396;
}
block_396:
{
lean_object* x_393; 
if (x_392 == 0)
{
x_393 = x_391;
goto block_394;
}
else
{
lean_object* x_395; 
x_395 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_395, 0, x_390);
x_393 = x_395;
goto block_394;
}
block_394:
{
return x_393;
}
}
}
}
else
{
lean_object* x_398; lean_object* x_399; uint8_t x_400; uint8_t x_405; 
lean_dec(x_358);
lean_dec_ref(x_356);
lean_dec(x_354);
lean_dec_ref(x_351);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_398 = lean_ctor_get(x_362, 0);
x_405 = !lean_is_exclusive(x_362);
if (x_405 == 0)
{
x_399 = x_362;
x_400 = x_405;
goto block_404;
}
else
{
lean_inc(x_398);
lean_dec(x_362);
x_399 = lean_box(0);
x_400 = x_405;
goto block_404;
}
block_404:
{
lean_object* x_401; 
if (x_400 == 0)
{
x_401 = x_399;
goto block_402;
}
else
{
lean_object* x_403; 
x_403 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_403, 0, x_398);
x_401 = x_403;
goto block_402;
}
block_402:
{
return x_401;
}
}
}
}
}
else
{
lean_object* x_406; lean_object* x_407; uint8_t x_408; uint8_t x_413; 
lean_dec(x_358);
lean_dec_ref(x_356);
lean_dec(x_354);
lean_dec_ref(x_351);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_406 = lean_ctor_get(x_359, 0);
x_413 = !lean_is_exclusive(x_359);
if (x_413 == 0)
{
x_407 = x_359;
x_408 = x_413;
goto block_412;
}
else
{
lean_inc(x_406);
lean_dec(x_359);
x_407 = lean_box(0);
x_408 = x_413;
goto block_412;
}
block_412:
{
lean_object* x_409; 
if (x_408 == 0)
{
x_409 = x_407;
goto block_410;
}
else
{
lean_object* x_411; 
x_411 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_411, 0, x_406);
x_409 = x_411;
goto block_410;
}
block_410:
{
return x_409;
}
}
}
}
block_465:
{
lean_object* x_421; 
lean_inc(x_419);
lean_inc_ref(x_418);
lean_inc(x_417);
lean_inc_ref(x_416);
lean_inc_ref(x_160);
x_421 = l_Lean_Meta_matchHEq_x3f(x_160, x_416, x_417, x_418, x_419);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
lean_dec_ref(x_421);
if (lean_obj_tag(x_422) == 1)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
lean_dec_ref(x_422);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_423, 0);
lean_inc(x_426);
lean_dec(x_423);
x_427 = lean_ctor_get(x_424, 0);
lean_inc(x_427);
lean_dec(x_424);
x_428 = lean_ctor_get(x_425, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_425, 1);
lean_inc(x_429);
lean_dec(x_425);
lean_inc(x_419);
lean_inc_ref(x_418);
lean_inc(x_417);
lean_inc_ref(x_416);
x_430 = l_Lean_Meta_matchConstructorApp_x3f(x_427, x_416, x_417, x_418, x_419);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
lean_dec_ref(x_430);
if (lean_obj_tag(x_431) == 1)
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
lean_dec_ref(x_431);
lean_inc(x_419);
lean_inc_ref(x_418);
lean_inc(x_417);
lean_inc_ref(x_416);
x_433 = l_Lean_Meta_matchConstructorApp_x3f(x_429, x_416, x_417, x_418, x_419);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
lean_dec_ref(x_433);
if (lean_obj_tag(x_434) == 1)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; 
x_435 = lean_ctor_get(x_432, 0);
lean_inc_ref(x_435);
lean_dec(x_432);
x_436 = lean_ctor_get(x_434, 0);
lean_inc(x_436);
lean_dec_ref(x_434);
x_437 = lean_ctor_get(x_436, 0);
lean_inc_ref(x_437);
lean_dec(x_436);
x_438 = lean_ctor_get(x_435, 0);
lean_inc(x_438);
lean_dec_ref(x_435);
x_439 = lean_ctor_get(x_437, 0);
lean_inc(x_439);
lean_dec_ref(x_437);
x_440 = lean_name_eq(x_438, x_439);
lean_dec(x_439);
lean_dec(x_438);
if (x_440 == 0)
{
x_351 = x_418;
x_352 = x_426;
x_353 = x_415;
x_354 = x_419;
x_355 = x_428;
x_356 = x_416;
x_357 = lean_box(0);
x_358 = x_417;
goto block_414;
}
else
{
if (x_111 == 0)
{
lean_dec(x_428);
lean_dec(x_426);
x_341 = x_415;
x_342 = x_12;
x_343 = x_416;
x_344 = x_417;
x_345 = x_418;
x_346 = x_419;
x_347 = lean_box(0);
goto block_350;
}
else
{
x_351 = x_418;
x_352 = x_426;
x_353 = x_415;
x_354 = x_419;
x_355 = x_428;
x_356 = x_416;
x_357 = lean_box(0);
x_358 = x_417;
goto block_414;
}
}
}
else
{
lean_dec(x_434);
lean_dec(x_432);
lean_dec(x_428);
lean_dec(x_426);
x_341 = x_415;
x_342 = x_12;
x_343 = x_416;
x_344 = x_417;
x_345 = x_418;
x_346 = x_419;
x_347 = lean_box(0);
goto block_350;
}
}
else
{
lean_object* x_441; lean_object* x_442; uint8_t x_443; uint8_t x_448; 
lean_dec(x_432);
lean_dec(x_428);
lean_dec(x_426);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_441 = lean_ctor_get(x_433, 0);
x_448 = !lean_is_exclusive(x_433);
if (x_448 == 0)
{
x_442 = x_433;
x_443 = x_448;
goto block_447;
}
else
{
lean_inc(x_441);
lean_dec(x_433);
x_442 = lean_box(0);
x_443 = x_448;
goto block_447;
}
block_447:
{
lean_object* x_444; 
if (x_443 == 0)
{
x_444 = x_442;
goto block_445;
}
else
{
lean_object* x_446; 
x_446 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_446, 0, x_441);
x_444 = x_446;
goto block_445;
}
block_445:
{
return x_444;
}
}
}
}
else
{
lean_dec(x_431);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_426);
x_341 = x_415;
x_342 = x_12;
x_343 = x_416;
x_344 = x_417;
x_345 = x_418;
x_346 = x_419;
x_347 = lean_box(0);
goto block_350;
}
}
else
{
lean_object* x_449; lean_object* x_450; uint8_t x_451; uint8_t x_456; 
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_426);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_449 = lean_ctor_get(x_430, 0);
x_456 = !lean_is_exclusive(x_430);
if (x_456 == 0)
{
x_450 = x_430;
x_451 = x_456;
goto block_455;
}
else
{
lean_inc(x_449);
lean_dec(x_430);
x_450 = lean_box(0);
x_451 = x_456;
goto block_455;
}
block_455:
{
lean_object* x_452; 
if (x_451 == 0)
{
x_452 = x_450;
goto block_453;
}
else
{
lean_object* x_454; 
x_454 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_454, 0, x_449);
x_452 = x_454;
goto block_453;
}
block_453:
{
return x_452;
}
}
}
}
else
{
lean_dec(x_422);
x_341 = x_415;
x_342 = x_111;
x_343 = x_416;
x_344 = x_417;
x_345 = x_418;
x_346 = x_419;
x_347 = lean_box(0);
goto block_350;
}
}
else
{
lean_object* x_457; lean_object* x_458; uint8_t x_459; uint8_t x_464; 
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_457 = lean_ctor_get(x_421, 0);
x_464 = !lean_is_exclusive(x_421);
if (x_464 == 0)
{
x_458 = x_421;
x_459 = x_464;
goto block_463;
}
else
{
lean_inc(x_457);
lean_dec(x_421);
x_458 = lean_box(0);
x_459 = x_464;
goto block_463;
}
block_463:
{
lean_object* x_460; 
if (x_459 == 0)
{
x_460 = x_458;
goto block_461;
}
else
{
lean_object* x_462; 
x_462 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_462, 0, x_457);
x_460 = x_462;
goto block_461;
}
block_461:
{
return x_460;
}
}
}
}
block_512:
{
lean_object* x_471; 
lean_inc(x_469);
lean_inc_ref(x_468);
lean_inc(x_467);
lean_inc_ref(x_466);
lean_inc_ref(x_160);
x_471 = l_Lean_Meta_matchEq_x3f(x_160, x_466, x_467, x_468, x_469);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; 
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
lean_dec_ref(x_471);
if (lean_obj_tag(x_472) == 1)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
lean_dec_ref(x_472);
x_474 = lean_ctor_get(x_473, 1);
lean_inc(x_474);
lean_dec(x_473);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec(x_474);
lean_inc(x_469);
lean_inc_ref(x_468);
lean_inc(x_467);
lean_inc_ref(x_466);
x_477 = l_Lean_Meta_matchConstructorApp_x3f(x_475, x_466, x_467, x_468, x_469);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
lean_dec_ref(x_477);
if (lean_obj_tag(x_478) == 1)
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
lean_dec_ref(x_478);
lean_inc(x_469);
lean_inc_ref(x_468);
lean_inc(x_467);
lean_inc_ref(x_466);
x_480 = l_Lean_Meta_matchConstructorApp_x3f(x_476, x_466, x_467, x_468, x_469);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
lean_dec_ref(x_480);
if (lean_obj_tag(x_481) == 1)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
x_482 = lean_ctor_get(x_479, 0);
lean_inc_ref(x_482);
lean_dec(x_479);
x_483 = lean_ctor_get(x_481, 0);
lean_inc(x_483);
lean_dec_ref(x_481);
x_484 = lean_ctor_get(x_483, 0);
lean_inc_ref(x_484);
lean_dec(x_483);
x_485 = lean_ctor_get(x_482, 0);
lean_inc(x_485);
lean_dec_ref(x_482);
x_486 = lean_ctor_get(x_484, 0);
lean_inc(x_486);
lean_dec_ref(x_484);
x_487 = lean_name_eq(x_485, x_486);
lean_dec(x_486);
lean_dec(x_485);
if (x_487 == 0)
{
lean_dec_ref(x_160);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_38 = lean_box(0);
x_39 = x_467;
x_40 = x_466;
x_41 = x_469;
x_42 = x_468;
goto block_79;
}
else
{
if (x_111 == 0)
{
lean_del_object(x_35);
x_415 = x_12;
x_416 = x_466;
x_417 = x_467;
x_418 = x_468;
x_419 = x_469;
x_420 = lean_box(0);
goto block_465;
}
else
{
lean_dec_ref(x_160);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_38 = lean_box(0);
x_39 = x_467;
x_40 = x_466;
x_41 = x_469;
x_42 = x_468;
goto block_79;
}
}
}
else
{
lean_dec(x_481);
lean_dec(x_479);
lean_del_object(x_35);
x_415 = x_12;
x_416 = x_466;
x_417 = x_467;
x_418 = x_468;
x_419 = x_469;
x_420 = lean_box(0);
goto block_465;
}
}
else
{
lean_object* x_488; lean_object* x_489; uint8_t x_490; uint8_t x_495; 
lean_dec(x_479);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_488 = lean_ctor_get(x_480, 0);
x_495 = !lean_is_exclusive(x_480);
if (x_495 == 0)
{
x_489 = x_480;
x_490 = x_495;
goto block_494;
}
else
{
lean_inc(x_488);
lean_dec(x_480);
x_489 = lean_box(0);
x_490 = x_495;
goto block_494;
}
block_494:
{
lean_object* x_491; 
if (x_490 == 0)
{
x_491 = x_489;
goto block_492;
}
else
{
lean_object* x_493; 
x_493 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_493, 0, x_488);
x_491 = x_493;
goto block_492;
}
block_492:
{
return x_491;
}
}
}
}
else
{
lean_dec(x_478);
lean_dec(x_476);
lean_del_object(x_35);
x_415 = x_12;
x_416 = x_466;
x_417 = x_467;
x_418 = x_468;
x_419 = x_469;
x_420 = lean_box(0);
goto block_465;
}
}
else
{
lean_object* x_496; lean_object* x_497; uint8_t x_498; uint8_t x_503; 
lean_dec(x_476);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_496 = lean_ctor_get(x_477, 0);
x_503 = !lean_is_exclusive(x_477);
if (x_503 == 0)
{
x_497 = x_477;
x_498 = x_503;
goto block_502;
}
else
{
lean_inc(x_496);
lean_dec(x_477);
x_497 = lean_box(0);
x_498 = x_503;
goto block_502;
}
block_502:
{
lean_object* x_499; 
if (x_498 == 0)
{
x_499 = x_497;
goto block_500;
}
else
{
lean_object* x_501; 
x_501 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_501, 0, x_496);
x_499 = x_501;
goto block_500;
}
block_500:
{
return x_499;
}
}
}
}
else
{
lean_dec(x_472);
lean_del_object(x_35);
x_415 = x_111;
x_416 = x_466;
x_417 = x_467;
x_418 = x_468;
x_419 = x_469;
x_420 = lean_box(0);
goto block_465;
}
}
else
{
lean_object* x_504; lean_object* x_505; uint8_t x_506; uint8_t x_511; 
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_504 = lean_ctor_get(x_471, 0);
x_511 = !lean_is_exclusive(x_471);
if (x_511 == 0)
{
x_505 = x_471;
x_506 = x_511;
goto block_510;
}
else
{
lean_inc(x_504);
lean_dec(x_471);
x_505 = lean_box(0);
x_506 = x_511;
goto block_510;
}
block_510:
{
lean_object* x_507; 
if (x_506 == 0)
{
x_507 = x_505;
goto block_508;
}
else
{
lean_object* x_509; 
x_509 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_509, 0, x_504);
x_507 = x_509;
goto block_508;
}
block_508:
{
return x_507;
}
}
}
}
block_650:
{
lean_object* x_518; 
lean_inc(x_516);
lean_inc_ref(x_515);
lean_inc(x_514);
lean_inc_ref(x_513);
lean_inc_ref(x_160);
x_518 = l_refutableHasNotBit_x3f(x_160, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
lean_dec_ref(x_518);
if (lean_obj_tag(x_519) == 1)
{
lean_object* x_520; lean_object* x_521; uint8_t x_522; uint8_t x_560; 
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_520 = lean_ctor_get(x_519, 0);
x_560 = !lean_is_exclusive(x_519);
if (x_560 == 0)
{
x_521 = x_519;
x_522 = x_560;
goto block_559;
}
else
{
lean_inc(x_520);
lean_dec(x_519);
x_521 = lean_box(0);
x_522 = x_560;
goto block_559;
}
block_559:
{
lean_object* x_523; 
lean_inc(x_2);
x_523 = l_Lean_MVarId_getType(x_2, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
lean_dec_ref(x_523);
x_525 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_514);
x_526 = l_Lean_Meta_mkAbsurd(x_524, x_520, x_525, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; 
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
lean_dec_ref(x_526);
x_528 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_527, x_514);
lean_dec(x_514);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; 
lean_dec_ref(x_528);
x_529 = lean_box(x_12);
if (x_522 == 0)
{
lean_ctor_set(x_521, 0, x_529);
x_530 = x_521;
goto block_533;
}
else
{
lean_object* x_534; 
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_529);
x_530 = x_534;
goto block_533;
}
block_533:
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_37);
x_532 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_532, 0, x_531);
x_17 = x_532;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_535; lean_object* x_536; uint8_t x_537; uint8_t x_542; 
lean_del_object(x_521);
lean_del_object(x_15);
lean_dec(x_14);
x_535 = lean_ctor_get(x_528, 0);
x_542 = !lean_is_exclusive(x_528);
if (x_542 == 0)
{
x_536 = x_528;
x_537 = x_542;
goto block_541;
}
else
{
lean_inc(x_535);
lean_dec(x_528);
x_536 = lean_box(0);
x_537 = x_542;
goto block_541;
}
block_541:
{
lean_object* x_538; 
if (x_537 == 0)
{
x_538 = x_536;
goto block_539;
}
else
{
lean_object* x_540; 
x_540 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_540, 0, x_535);
x_538 = x_540;
goto block_539;
}
block_539:
{
return x_538;
}
}
}
}
else
{
lean_object* x_543; lean_object* x_544; uint8_t x_545; uint8_t x_550; 
lean_del_object(x_521);
lean_dec(x_514);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_543 = lean_ctor_get(x_526, 0);
x_550 = !lean_is_exclusive(x_526);
if (x_550 == 0)
{
x_544 = x_526;
x_545 = x_550;
goto block_549;
}
else
{
lean_inc(x_543);
lean_dec(x_526);
x_544 = lean_box(0);
x_545 = x_550;
goto block_549;
}
block_549:
{
lean_object* x_546; 
if (x_545 == 0)
{
x_546 = x_544;
goto block_547;
}
else
{
lean_object* x_548; 
x_548 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_548, 0, x_543);
x_546 = x_548;
goto block_547;
}
block_547:
{
return x_546;
}
}
}
}
else
{
lean_object* x_551; lean_object* x_552; uint8_t x_553; uint8_t x_558; 
lean_del_object(x_521);
lean_dec(x_520);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_551 = lean_ctor_get(x_523, 0);
x_558 = !lean_is_exclusive(x_523);
if (x_558 == 0)
{
x_552 = x_523;
x_553 = x_558;
goto block_557;
}
else
{
lean_inc(x_551);
lean_dec(x_523);
x_552 = lean_box(0);
x_553 = x_558;
goto block_557;
}
block_557:
{
lean_object* x_554; 
if (x_553 == 0)
{
x_554 = x_552;
goto block_555;
}
else
{
lean_object* x_556; 
x_556 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_556, 0, x_551);
x_554 = x_556;
goto block_555;
}
block_555:
{
return x_554;
}
}
}
}
}
else
{
lean_object* x_561; 
lean_dec(x_519);
lean_inc(x_516);
lean_inc_ref(x_515);
lean_inc(x_514);
lean_inc_ref(x_513);
lean_inc_ref(x_160);
x_561 = l_Lean_Meta_matchNe_x3f(x_160, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
lean_dec_ref(x_561);
if (lean_obj_tag(x_562) == 1)
{
lean_object* x_563; lean_object* x_564; uint8_t x_565; uint8_t x_633; 
x_563 = lean_ctor_get(x_562, 0);
x_633 = !lean_is_exclusive(x_562);
if (x_633 == 0)
{
x_564 = x_562;
x_565 = x_633;
goto block_632;
}
else
{
lean_inc(x_563);
lean_dec(x_562);
x_564 = lean_box(0);
x_565 = x_633;
goto block_632;
}
block_632:
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; uint8_t x_631; 
x_566 = lean_ctor_get(x_563, 1);
lean_inc(x_566);
lean_dec(x_563);
x_567 = lean_ctor_get(x_566, 0);
x_568 = lean_ctor_get(x_566, 1);
x_631 = !lean_is_exclusive(x_566);
if (x_631 == 0)
{
x_569 = x_566;
x_570 = x_631;
goto block_630;
}
else
{
lean_inc(x_568);
lean_inc(x_567);
lean_dec(x_566);
x_569 = lean_box(0);
x_570 = x_631;
goto block_630;
}
block_630:
{
lean_object* x_571; 
lean_inc(x_516);
lean_inc_ref(x_515);
lean_inc(x_514);
lean_inc_ref(x_513);
lean_inc(x_567);
x_571 = l_Lean_Meta_isExprDefEq(x_567, x_568, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; uint8_t x_573; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec_ref(x_571);
x_573 = lean_unbox(x_572);
lean_dec(x_572);
if (x_573 == 0)
{
lean_del_object(x_569);
lean_dec(x_567);
lean_del_object(x_564);
x_466 = x_513;
x_467 = x_514;
x_468 = x_515;
x_469 = x_516;
x_470 = lean_box(0);
goto block_512;
}
else
{
lean_object* x_574; 
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_574 = l_Lean_MVarId_getType(x_2, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
lean_dec_ref(x_574);
lean_inc(x_516);
lean_inc_ref(x_515);
lean_inc(x_514);
lean_inc_ref(x_513);
x_576 = l_Lean_Meta_mkEqRefl(x_567, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
lean_dec_ref(x_576);
x_578 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_514);
x_579 = l_Lean_Meta_mkAbsurd(x_575, x_577, x_578, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
lean_dec_ref(x_579);
x_581 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_580, x_514);
lean_dec(x_514);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; 
lean_dec_ref(x_581);
x_582 = lean_box(x_12);
if (x_565 == 0)
{
lean_ctor_set(x_564, 0, x_582);
x_583 = x_564;
goto block_588;
}
else
{
lean_object* x_589; 
x_589 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_589, 0, x_582);
x_583 = x_589;
goto block_588;
}
block_588:
{
lean_object* x_584; 
if (x_570 == 0)
{
lean_ctor_set(x_569, 1, x_37);
lean_ctor_set(x_569, 0, x_583);
x_584 = x_569;
goto block_586;
}
else
{
lean_object* x_587; 
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_583);
lean_ctor_set(x_587, 1, x_37);
x_584 = x_587;
goto block_586;
}
block_586:
{
lean_object* x_585; 
x_585 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_585, 0, x_584);
x_17 = x_585;
x_18 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_590; lean_object* x_591; uint8_t x_592; uint8_t x_597; 
lean_del_object(x_569);
lean_del_object(x_564);
lean_del_object(x_15);
lean_dec(x_14);
x_590 = lean_ctor_get(x_581, 0);
x_597 = !lean_is_exclusive(x_581);
if (x_597 == 0)
{
x_591 = x_581;
x_592 = x_597;
goto block_596;
}
else
{
lean_inc(x_590);
lean_dec(x_581);
x_591 = lean_box(0);
x_592 = x_597;
goto block_596;
}
block_596:
{
lean_object* x_593; 
if (x_592 == 0)
{
x_593 = x_591;
goto block_594;
}
else
{
lean_object* x_595; 
x_595 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_595, 0, x_590);
x_593 = x_595;
goto block_594;
}
block_594:
{
return x_593;
}
}
}
}
else
{
lean_object* x_598; lean_object* x_599; uint8_t x_600; uint8_t x_605; 
lean_del_object(x_569);
lean_del_object(x_564);
lean_dec(x_514);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_598 = lean_ctor_get(x_579, 0);
x_605 = !lean_is_exclusive(x_579);
if (x_605 == 0)
{
x_599 = x_579;
x_600 = x_605;
goto block_604;
}
else
{
lean_inc(x_598);
lean_dec(x_579);
x_599 = lean_box(0);
x_600 = x_605;
goto block_604;
}
block_604:
{
lean_object* x_601; 
if (x_600 == 0)
{
x_601 = x_599;
goto block_602;
}
else
{
lean_object* x_603; 
x_603 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_603, 0, x_598);
x_601 = x_603;
goto block_602;
}
block_602:
{
return x_601;
}
}
}
}
else
{
lean_object* x_606; lean_object* x_607; uint8_t x_608; uint8_t x_613; 
lean_dec(x_575);
lean_del_object(x_569);
lean_del_object(x_564);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_606 = lean_ctor_get(x_576, 0);
x_613 = !lean_is_exclusive(x_576);
if (x_613 == 0)
{
x_607 = x_576;
x_608 = x_613;
goto block_612;
}
else
{
lean_inc(x_606);
lean_dec(x_576);
x_607 = lean_box(0);
x_608 = x_613;
goto block_612;
}
block_612:
{
lean_object* x_609; 
if (x_608 == 0)
{
x_609 = x_607;
goto block_610;
}
else
{
lean_object* x_611; 
x_611 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_611, 0, x_606);
x_609 = x_611;
goto block_610;
}
block_610:
{
return x_609;
}
}
}
}
else
{
lean_object* x_614; lean_object* x_615; uint8_t x_616; uint8_t x_621; 
lean_del_object(x_569);
lean_dec(x_567);
lean_del_object(x_564);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_614 = lean_ctor_get(x_574, 0);
x_621 = !lean_is_exclusive(x_574);
if (x_621 == 0)
{
x_615 = x_574;
x_616 = x_621;
goto block_620;
}
else
{
lean_inc(x_614);
lean_dec(x_574);
x_615 = lean_box(0);
x_616 = x_621;
goto block_620;
}
block_620:
{
lean_object* x_617; 
if (x_616 == 0)
{
x_617 = x_615;
goto block_618;
}
else
{
lean_object* x_619; 
x_619 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_619, 0, x_614);
x_617 = x_619;
goto block_618;
}
block_618:
{
return x_617;
}
}
}
}
}
else
{
lean_object* x_622; lean_object* x_623; uint8_t x_624; uint8_t x_629; 
lean_del_object(x_569);
lean_dec(x_567);
lean_del_object(x_564);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_622 = lean_ctor_get(x_571, 0);
x_629 = !lean_is_exclusive(x_571);
if (x_629 == 0)
{
x_623 = x_571;
x_624 = x_629;
goto block_628;
}
else
{
lean_inc(x_622);
lean_dec(x_571);
x_623 = lean_box(0);
x_624 = x_629;
goto block_628;
}
block_628:
{
lean_object* x_625; 
if (x_624 == 0)
{
x_625 = x_623;
goto block_626;
}
else
{
lean_object* x_627; 
x_627 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_627, 0, x_622);
x_625 = x_627;
goto block_626;
}
block_626:
{
return x_625;
}
}
}
}
}
}
else
{
lean_dec(x_562);
x_466 = x_513;
x_467 = x_514;
x_468 = x_515;
x_469 = x_516;
x_470 = lean_box(0);
goto block_512;
}
}
else
{
lean_object* x_634; lean_object* x_635; uint8_t x_636; uint8_t x_641; 
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_634 = lean_ctor_get(x_561, 0);
x_641 = !lean_is_exclusive(x_561);
if (x_641 == 0)
{
x_635 = x_561;
x_636 = x_641;
goto block_640;
}
else
{
lean_inc(x_634);
lean_dec(x_561);
x_635 = lean_box(0);
x_636 = x_641;
goto block_640;
}
block_640:
{
lean_object* x_637; 
if (x_636 == 0)
{
x_637 = x_635;
goto block_638;
}
else
{
lean_object* x_639; 
x_639 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_639, 0, x_634);
x_637 = x_639;
goto block_638;
}
block_638:
{
return x_637;
}
}
}
}
}
else
{
lean_object* x_642; lean_object* x_643; uint8_t x_644; uint8_t x_649; 
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_642 = lean_ctor_get(x_518, 0);
x_649 = !lean_is_exclusive(x_518);
if (x_649 == 0)
{
x_643 = x_518;
x_644 = x_649;
goto block_648;
}
else
{
lean_inc(x_642);
lean_dec(x_518);
x_643 = lean_box(0);
x_644 = x_649;
goto block_648;
}
block_648:
{
lean_object* x_645; 
if (x_644 == 0)
{
x_645 = x_643;
goto block_646;
}
else
{
lean_object* x_647; 
x_647 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_647, 0, x_642);
x_645 = x_647;
goto block_646;
}
block_646:
{
return x_645;
}
}
}
}
}
else
{
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_80;
x_27 = lean_box(0);
goto block_32;
}
block_79:
{
lean_object* x_43; 
lean_inc(x_2);
x_43 = l_Lean_MVarId_getType(x_2, x_40, x_39, x_42, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_39);
x_46 = l_Lean_Meta_mkNoConfusion(x_44, x_45, x_40, x_39, x_42, x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_47, x_39);
lean_dec(x_39);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_48);
x_49 = lean_box(x_12);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_49);
x_50 = x_35;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_50 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_37);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_17 = x_52;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_del_object(x_35);
lean_del_object(x_15);
lean_dec(x_14);
x_55 = lean_ctor_get(x_48, 0);
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
x_56 = x_48;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec(x_39);
lean_del_object(x_35);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_63 = lean_ctor_get(x_46, 0);
x_70 = !lean_is_exclusive(x_46);
if (x_70 == 0)
{
x_64 = x_46;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_46);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_71 = lean_ctor_get(x_43, 0);
x_78 = !lean_is_exclusive(x_43);
if (x_78 == 0)
{
x_72 = x_43;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_43);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
block_103:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_1, 0);
x_87 = l_Lean_LocalDecl_fvarId(x_34);
lean_dec(x_34);
lean_inc(x_86);
lean_inc(x_2);
x_88 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_2, x_87, x_86, x_82, x_85, x_84, x_81);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_80;
x_27 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_91 = lean_box(x_12);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_37);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_17 = x_94;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_102; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = lean_ctor_get(x_88, 0);
x_102 = !lean_is_exclusive(x_88);
if (x_102 == 0)
{
x_96 = x_88;
x_97 = x_102;
goto block_101;
}
else
{
lean_inc(x_95);
lean_dec(x_88);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
block_110:
{
if (x_109 == 0)
{
lean_dec_ref(x_108);
lean_dec(x_107);
lean_dec_ref(x_105);
lean_dec(x_104);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_80;
x_27 = lean_box(0);
goto block_32;
}
else
{
x_81 = x_104;
x_82 = x_105;
x_83 = lean_box(0);
x_84 = x_108;
x_85 = x_107;
goto block_103;
}
}
block_118:
{
if (x_113 == 0)
{
x_81 = x_112;
x_82 = x_114;
x_83 = lean_box(0);
x_84 = x_117;
x_85 = x_116;
goto block_103;
}
else
{
x_104 = x_112;
x_105 = x_114;
x_106 = lean_box(0);
x_107 = x_116;
x_108 = x_117;
x_109 = x_111;
goto block_110;
}
}
block_126:
{
if (x_125 == 0)
{
x_104 = x_119;
x_105 = x_121;
x_106 = lean_box(0);
x_107 = x_124;
x_108 = x_123;
x_109 = x_111;
goto block_110;
}
else
{
x_112 = x_119;
x_113 = x_120;
x_114 = x_121;
x_115 = lean_box(0);
x_116 = x_124;
x_117 = x_123;
goto block_118;
}
}
block_135:
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_134 == 0)
{
x_119 = x_132;
x_120 = x_128;
x_121 = x_129;
x_122 = lean_box(0);
x_123 = x_131;
x_124 = x_130;
x_125 = x_111;
goto block_126;
}
else
{
if (x_127 == 0)
{
x_112 = x_132;
x_113 = x_128;
x_114 = x_129;
x_115 = lean_box(0);
x_116 = x_130;
x_117 = x_131;
goto block_118;
}
else
{
x_119 = x_132;
x_120 = x_128;
x_121 = x_129;
x_122 = lean_box(0);
x_123 = x_131;
x_124 = x_130;
x_125 = x_111;
goto block_126;
}
}
}
block_159:
{
if (x_143 == 0)
{
x_127 = x_137;
x_128 = x_136;
x_129 = x_139;
x_130 = x_141;
x_131 = x_140;
x_132 = x_138;
x_133 = lean_box(0);
goto block_135;
}
else
{
lean_object* x_144; 
lean_inc(x_138);
lean_inc_ref(x_140);
lean_inc(x_141);
lean_inc_ref(x_139);
lean_inc(x_34);
lean_inc(x_2);
x_144 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_2, x_34, x_139, x_141, x_140, x_138);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
x_127 = x_137;
x_128 = x_136;
x_129 = x_139;
x_130 = x_141;
x_131 = x_140;
x_132 = x_138;
x_133 = lean_box(0);
goto block_135;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_139);
lean_dec(x_138);
lean_dec(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_147 = lean_box(x_12);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_37);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_17 = x_150;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_158; 
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec_ref(x_139);
lean_dec(x_138);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_151 = lean_ctor_get(x_144, 0);
x_158 = !lean_is_exclusive(x_144);
if (x_158 == 0)
{
x_152 = x_144;
x_153 = x_158;
goto block_157;
}
else
{
lean_inc(x_151);
lean_dec(x_144);
x_152 = lean_box(0);
x_153 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_154; 
if (x_153 == 0)
{
x_154 = x_152;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_151);
x_154 = x_156;
goto block_155;
}
block_155:
{
return x_154;
}
}
}
}
}
}
}
block_24:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_14);
x_20 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
block_32:
{
lean_object* x_28; size_t x_29; size_t x_30; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
x_29 = 1;
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
x_6 = x_28;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_724; 
x_14 = lean_ctor_get(x_6, 1);
x_724 = !lean_is_exclusive(x_6);
if (x_724 == 0)
{
lean_object* x_725; 
x_725 = lean_ctor_get(x_6, 0);
lean_dec(x_725);
x_15 = x_6;
x_16 = x_724;
goto block_723;
}
else
{
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_724;
goto block_723;
}
block_723:
{
lean_object* x_17; lean_object* x_18; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_33; 
x_25 = lean_box(0);
x_33 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_33) == 0)
{
lean_del_object(x_15);
x_26 = x_14;
x_27 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_722; 
x_34 = lean_ctor_get(x_33, 0);
x_722 = !lean_is_exclusive(x_33);
if (x_722 == 0)
{
x_35 = x_33;
x_36 = x_722;
goto block_721;
}
else
{
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = x_722;
goto block_721;
}
block_721:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; uint8_t x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; uint8_t x_143; 
x_37 = lean_box(0);
x_80 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
x_111 = l_Lean_LocalDecl_isImplementationDetail(x_34);
if (x_111 == 0)
{
lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; uint8_t x_179; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; uint8_t x_299; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; uint8_t x_309; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; uint8_t x_319; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; uint8_t x_339; uint8_t x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_651; 
x_160 = l_Lean_LocalDecl_type(x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_160);
x_651 = l_Lean_Meta_matchNot_x3f(x_160, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
lean_dec_ref(x_651);
if (lean_obj_tag(x_652) == 1)
{
lean_object* x_653; lean_object* x_654; uint8_t x_655; uint8_t x_712; 
x_653 = lean_ctor_get(x_652, 0);
x_712 = !lean_is_exclusive(x_652);
if (x_712 == 0)
{
x_654 = x_652;
x_655 = x_712;
goto block_711;
}
else
{
lean_inc(x_653);
lean_dec(x_652);
x_654 = lean_box(0);
x_655 = x_712;
goto block_711;
}
block_711:
{
lean_object* x_656; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_656 = l_Lean_Meta_findLocalDeclWithType_x3f(x_653, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
lean_dec_ref(x_656);
if (lean_obj_tag(x_657) == 1)
{
lean_object* x_658; lean_object* x_659; uint8_t x_660; uint8_t x_702; 
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec_ref(x_1);
x_658 = lean_ctor_get(x_657, 0);
x_702 = !lean_is_exclusive(x_657);
if (x_702 == 0)
{
x_659 = x_657;
x_660 = x_702;
goto block_701;
}
else
{
lean_inc(x_658);
lean_dec(x_657);
x_659 = lean_box(0);
x_660 = x_702;
goto block_701;
}
block_701:
{
lean_object* x_661; 
lean_inc(x_2);
x_661 = l_Lean_MVarId_getType(x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
lean_dec_ref(x_661);
x_663 = l_Lean_LocalDecl_toExpr(x_34);
x_664 = l_Lean_mkFVar(x_658);
x_665 = l_Lean_Expr_app___override(x_663, x_664);
lean_inc(x_8);
x_666 = l_Lean_Meta_mkFalseElim(x_662, x_665, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
lean_dec_ref(x_666);
x_668 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_667, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; 
lean_dec_ref(x_668);
x_669 = lean_box(x_12);
if (x_660 == 0)
{
lean_ctor_set(x_659, 0, x_669);
x_670 = x_659;
goto block_675;
}
else
{
lean_object* x_676; 
x_676 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_676, 0, x_669);
x_670 = x_676;
goto block_675;
}
block_675:
{
lean_object* x_671; lean_object* x_672; 
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_37);
if (x_655 == 0)
{
lean_ctor_set_tag(x_654, 0);
lean_ctor_set(x_654, 0, x_671);
x_672 = x_654;
goto block_673;
}
else
{
lean_object* x_674; 
x_674 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_674, 0, x_671);
x_672 = x_674;
goto block_673;
}
block_673:
{
x_17 = x_672;
x_18 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_677; lean_object* x_678; uint8_t x_679; uint8_t x_684; 
lean_del_object(x_659);
lean_del_object(x_654);
lean_del_object(x_15);
lean_dec(x_14);
x_677 = lean_ctor_get(x_668, 0);
x_684 = !lean_is_exclusive(x_668);
if (x_684 == 0)
{
x_678 = x_668;
x_679 = x_684;
goto block_683;
}
else
{
lean_inc(x_677);
lean_dec(x_668);
x_678 = lean_box(0);
x_679 = x_684;
goto block_683;
}
block_683:
{
lean_object* x_680; 
if (x_679 == 0)
{
x_680 = x_678;
goto block_681;
}
else
{
lean_object* x_682; 
x_682 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_682, 0, x_677);
x_680 = x_682;
goto block_681;
}
block_681:
{
return x_680;
}
}
}
}
else
{
lean_object* x_685; lean_object* x_686; uint8_t x_687; uint8_t x_692; 
lean_del_object(x_659);
lean_del_object(x_654);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
x_685 = lean_ctor_get(x_666, 0);
x_692 = !lean_is_exclusive(x_666);
if (x_692 == 0)
{
x_686 = x_666;
x_687 = x_692;
goto block_691;
}
else
{
lean_inc(x_685);
lean_dec(x_666);
x_686 = lean_box(0);
x_687 = x_692;
goto block_691;
}
block_691:
{
lean_object* x_688; 
if (x_687 == 0)
{
x_688 = x_686;
goto block_689;
}
else
{
lean_object* x_690; 
x_690 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_690, 0, x_685);
x_688 = x_690;
goto block_689;
}
block_689:
{
return x_688;
}
}
}
}
else
{
lean_object* x_693; lean_object* x_694; uint8_t x_695; uint8_t x_700; 
lean_del_object(x_659);
lean_dec(x_658);
lean_del_object(x_654);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_693 = lean_ctor_get(x_661, 0);
x_700 = !lean_is_exclusive(x_661);
if (x_700 == 0)
{
x_694 = x_661;
x_695 = x_700;
goto block_699;
}
else
{
lean_inc(x_693);
lean_dec(x_661);
x_694 = lean_box(0);
x_695 = x_700;
goto block_699;
}
block_699:
{
lean_object* x_696; 
if (x_695 == 0)
{
x_696 = x_694;
goto block_697;
}
else
{
lean_object* x_698; 
x_698 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_698, 0, x_693);
x_696 = x_698;
goto block_697;
}
block_697:
{
return x_696;
}
}
}
}
}
else
{
lean_dec(x_657);
lean_del_object(x_654);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_513 = x_7;
x_514 = x_8;
x_515 = x_9;
x_516 = x_10;
x_517 = lean_box(0);
goto block_650;
}
}
else
{
lean_object* x_703; lean_object* x_704; uint8_t x_705; uint8_t x_710; 
lean_del_object(x_654);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_703 = lean_ctor_get(x_656, 0);
x_710 = !lean_is_exclusive(x_656);
if (x_710 == 0)
{
x_704 = x_656;
x_705 = x_710;
goto block_709;
}
else
{
lean_inc(x_703);
lean_dec(x_656);
x_704 = lean_box(0);
x_705 = x_710;
goto block_709;
}
block_709:
{
lean_object* x_706; 
if (x_705 == 0)
{
x_706 = x_704;
goto block_707;
}
else
{
lean_object* x_708; 
x_708 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_708, 0, x_703);
x_706 = x_708;
goto block_707;
}
block_707:
{
return x_706;
}
}
}
}
}
else
{
lean_dec(x_652);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_513 = x_7;
x_514 = x_8;
x_515 = x_9;
x_516 = x_10;
x_517 = lean_box(0);
goto block_650;
}
}
else
{
lean_object* x_713; lean_object* x_714; uint8_t x_715; uint8_t x_720; 
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_713 = lean_ctor_get(x_651, 0);
x_720 = !lean_is_exclusive(x_651);
if (x_720 == 0)
{
x_714 = x_651;
x_715 = x_720;
goto block_719;
}
else
{
lean_inc(x_713);
lean_dec(x_651);
x_714 = lean_box(0);
x_715 = x_720;
goto block_719;
}
block_719:
{
lean_object* x_716; 
if (x_715 == 0)
{
x_716 = x_714;
goto block_717;
}
else
{
lean_object* x_718; 
x_718 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_718, 0, x_713);
x_716 = x_718;
goto block_717;
}
block_717:
{
return x_716;
}
}
}
block_170:
{
uint8_t x_168; 
x_168 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_168 == 0)
{
lean_dec_ref(x_160);
x_136 = x_165;
x_137 = x_161;
x_138 = x_163;
x_139 = x_166;
x_140 = x_164;
x_141 = x_162;
x_142 = lean_box(0);
x_143 = x_111;
goto block_159;
}
else
{
uint8_t x_169; 
x_169 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_160);
x_136 = x_165;
x_137 = x_161;
x_138 = x_163;
x_139 = x_166;
x_140 = x_164;
x_141 = x_162;
x_142 = lean_box(0);
x_143 = x_169;
goto block_159;
}
}
block_181:
{
if (x_179 == 0)
{
lean_dec_ref(x_177);
x_161 = x_175;
x_162 = x_178;
x_163 = x_172;
x_164 = x_176;
x_165 = x_171;
x_166 = x_174;
x_167 = lean_box(0);
goto block_170;
}
else
{
lean_object* x_180; 
lean_dec(x_176);
lean_dec(x_174);
lean_dec_ref(x_172);
lean_dec_ref(x_171);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_177);
return x_180;
}
}
block_192:
{
uint8_t x_190; 
x_190 = l_Lean_Exception_isInterrupt(x_188);
if (x_190 == 0)
{
uint8_t x_191; 
lean_inc_ref(x_188);
x_191 = l_Lean_Exception_isRuntime(x_188);
x_171 = x_182;
x_172 = x_183;
x_173 = lean_box(0);
x_174 = x_184;
x_175 = x_185;
x_176 = x_186;
x_177 = x_188;
x_178 = x_187;
x_179 = x_191;
goto block_181;
}
else
{
x_171 = x_182;
x_172 = x_183;
x_173 = lean_box(0);
x_174 = x_184;
x_175 = x_185;
x_176 = x_186;
x_177 = x_188;
x_178 = x_187;
x_179 = x_190;
goto block_181;
}
}
block_291:
{
lean_object* x_200; 
lean_inc(x_196);
lean_inc_ref(x_193);
lean_inc(x_198);
lean_inc_ref(x_195);
lean_inc_ref(x_160);
x_200 = l_Lean_Meta_mkDecide(x_160, x_195, x_198, x_193, x_196);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; uint8_t x_289; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec_ref(x_200);
x_202 = l_Lean_Meta_Context_config(x_195);
x_203 = lean_ctor_get_uint8(x_202, 0);
x_204 = lean_ctor_get_uint8(x_202, 1);
x_205 = lean_ctor_get_uint8(x_202, 2);
x_206 = lean_ctor_get_uint8(x_202, 3);
x_207 = lean_ctor_get_uint8(x_202, 4);
x_208 = lean_ctor_get_uint8(x_202, 5);
x_209 = lean_ctor_get_uint8(x_202, 6);
x_210 = lean_ctor_get_uint8(x_202, 7);
x_211 = lean_ctor_get_uint8(x_202, 8);
x_212 = lean_ctor_get_uint8(x_202, 10);
x_213 = lean_ctor_get_uint8(x_202, 11);
x_214 = lean_ctor_get_uint8(x_202, 12);
x_215 = lean_ctor_get_uint8(x_202, 13);
x_216 = lean_ctor_get_uint8(x_202, 14);
x_217 = lean_ctor_get_uint8(x_202, 15);
x_218 = lean_ctor_get_uint8(x_202, 16);
x_219 = lean_ctor_get_uint8(x_202, 17);
x_220 = lean_ctor_get_uint8(x_202, 18);
x_289 = !lean_is_exclusive(x_202);
if (x_289 == 0)
{
x_221 = x_202;
x_222 = x_289;
goto block_288;
}
else
{
lean_dec(x_202);
x_221 = lean_box(0);
x_222 = x_289;
goto block_288;
}
block_288:
{
uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; lean_object* x_234; 
x_223 = lean_ctor_get_uint8(x_195, sizeof(void*)*7);
x_224 = lean_ctor_get(x_195, 1);
x_225 = lean_ctor_get(x_195, 2);
x_226 = lean_ctor_get(x_195, 3);
x_227 = lean_ctor_get(x_195, 4);
x_228 = lean_ctor_get(x_195, 5);
x_229 = lean_ctor_get(x_195, 6);
x_230 = lean_ctor_get_uint8(x_195, sizeof(void*)*7 + 1);
x_231 = lean_ctor_get_uint8(x_195, sizeof(void*)*7 + 2);
x_232 = lean_ctor_get_uint8(x_195, sizeof(void*)*7 + 3);
x_233 = 1;
if (x_222 == 0)
{
x_234 = x_221;
goto block_286;
}
else
{
lean_object* x_287; 
x_287 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_287, 0, x_203);
lean_ctor_set_uint8(x_287, 1, x_204);
lean_ctor_set_uint8(x_287, 2, x_205);
lean_ctor_set_uint8(x_287, 3, x_206);
lean_ctor_set_uint8(x_287, 4, x_207);
lean_ctor_set_uint8(x_287, 5, x_208);
lean_ctor_set_uint8(x_287, 6, x_209);
lean_ctor_set_uint8(x_287, 7, x_210);
lean_ctor_set_uint8(x_287, 8, x_211);
lean_ctor_set_uint8(x_287, 10, x_212);
lean_ctor_set_uint8(x_287, 11, x_213);
lean_ctor_set_uint8(x_287, 12, x_214);
lean_ctor_set_uint8(x_287, 13, x_215);
lean_ctor_set_uint8(x_287, 14, x_216);
lean_ctor_set_uint8(x_287, 15, x_217);
lean_ctor_set_uint8(x_287, 16, x_218);
lean_ctor_set_uint8(x_287, 17, x_219);
lean_ctor_set_uint8(x_287, 18, x_220);
x_234 = x_287;
goto block_286;
}
block_286:
{
uint64_t x_235; uint64_t x_236; uint64_t x_237; uint64_t x_238; uint64_t x_239; uint64_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_ctor_set_uint8(x_234, 9, x_233);
x_235 = l_Lean_Meta_Context_configKey(x_195);
x_236 = 2;
x_237 = lean_uint64_shift_right(x_235, x_236);
x_238 = lean_uint64_shift_left(x_237, x_236);
x_239 = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
x_240 = lean_uint64_lor(x_238, x_239);
x_241 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_241, 0, x_234);
lean_ctor_set_uint64(x_241, sizeof(void*)*1, x_240);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc_ref(x_226);
lean_inc_ref(x_225);
lean_inc(x_224);
x_242 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_224);
lean_ctor_set(x_242, 2, x_225);
lean_ctor_set(x_242, 3, x_226);
lean_ctor_set(x_242, 4, x_227);
lean_ctor_set(x_242, 5, x_228);
lean_ctor_set(x_242, 6, x_229);
lean_ctor_set_uint8(x_242, sizeof(void*)*7, x_223);
lean_ctor_set_uint8(x_242, sizeof(void*)*7 + 1, x_230);
lean_ctor_set_uint8(x_242, sizeof(void*)*7 + 2, x_231);
lean_ctor_set_uint8(x_242, sizeof(void*)*7 + 3, x_232);
lean_inc(x_196);
lean_inc_ref(x_193);
lean_inc(x_198);
lean_inc(x_201);
x_243 = lean_whnf(x_201, x_242, x_198, x_193, x_196);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
x_246 = l_Lean_Expr_isConstOf(x_244, x_245);
lean_dec(x_244);
if (x_246 == 0)
{
lean_dec(x_201);
x_161 = x_197;
x_162 = x_199;
x_163 = x_195;
x_164 = x_198;
x_165 = x_193;
x_166 = x_196;
x_167 = lean_box(0);
goto block_170;
}
else
{
lean_object* x_247; 
lean_inc(x_196);
lean_inc_ref(x_193);
lean_inc(x_198);
lean_inc_ref(x_195);
lean_inc(x_201);
x_247 = l_Lean_Meta_mkEqRefl(x_201, x_195, x_198, x_193, x_196);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
lean_dec_ref(x_247);
lean_inc(x_2);
x_249 = l_Lean_MVarId_getType(x_2, x_195, x_198, x_193, x_196);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec_ref(x_249);
x_251 = l_Lean_Expr_getAppNumArgs(x_201);
x_252 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
x_253 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(x_251);
x_254 = lean_mk_array(x_251, x_253);
x_255 = lean_unsigned_to_nat(1u);
x_256 = lean_nat_sub(x_251, x_255);
lean_dec(x_251);
x_257 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_201, x_254, x_256);
x_258 = lean_array_push(x_257, x_248);
x_259 = l_Lean_mkAppN(x_252, x_258);
lean_dec_ref(x_258);
lean_inc(x_34);
x_260 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_196);
lean_inc_ref(x_193);
lean_inc(x_198);
lean_inc_ref(x_195);
x_261 = l_Lean_Meta_mkAbsurd(x_250, x_260, x_259, x_195, x_198, x_193, x_196);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_281; 
x_262 = lean_ctor_get(x_261, 0);
x_281 = !lean_is_exclusive(x_261);
if (x_281 == 0)
{
x_263 = x_261;
x_264 = x_281;
goto block_280;
}
else
{
lean_inc(x_262);
lean_dec(x_261);
x_263 = lean_box(0);
x_264 = x_281;
goto block_280;
}
block_280:
{
lean_object* x_265; 
lean_inc(x_2);
x_265 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_262, x_198);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; uint8_t x_267; uint8_t x_277; 
lean_dec(x_198);
lean_dec(x_196);
lean_dec_ref(x_195);
lean_dec_ref(x_193);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_277 = !lean_is_exclusive(x_265);
if (x_277 == 0)
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_265, 0);
lean_dec(x_278);
x_266 = x_265;
x_267 = x_277;
goto block_276;
}
else
{
lean_dec(x_265);
x_266 = lean_box(0);
x_267 = x_277;
goto block_276;
}
block_276:
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_box(x_12);
if (x_267 == 0)
{
lean_ctor_set_tag(x_266, 1);
lean_ctor_set(x_266, 0, x_268);
x_269 = x_266;
goto block_274;
}
else
{
lean_object* x_275; 
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_268);
x_269 = x_275;
goto block_274;
}
block_274:
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_37);
if (x_264 == 0)
{
lean_ctor_set(x_263, 0, x_270);
x_271 = x_263;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_270);
x_271 = x_273;
goto block_272;
}
block_272:
{
x_17 = x_271;
x_18 = lean_box(0);
goto block_24;
}
}
}
}
else
{
lean_object* x_279; 
lean_del_object(x_263);
x_279 = lean_ctor_get(x_265, 0);
lean_inc(x_279);
lean_dec_ref(x_265);
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_197;
x_186 = x_198;
x_187 = x_199;
x_188 = x_279;
x_189 = lean_box(0);
goto block_192;
}
}
}
else
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_261, 0);
lean_inc(x_282);
lean_dec_ref(x_261);
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_197;
x_186 = x_198;
x_187 = x_199;
x_188 = x_282;
x_189 = lean_box(0);
goto block_192;
}
}
else
{
lean_object* x_283; 
lean_dec(x_248);
lean_dec(x_201);
x_283 = lean_ctor_get(x_249, 0);
lean_inc(x_283);
lean_dec_ref(x_249);
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_197;
x_186 = x_198;
x_187 = x_199;
x_188 = x_283;
x_189 = lean_box(0);
goto block_192;
}
}
else
{
lean_object* x_284; 
lean_dec(x_201);
x_284 = lean_ctor_get(x_247, 0);
lean_inc(x_284);
lean_dec_ref(x_247);
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_197;
x_186 = x_198;
x_187 = x_199;
x_188 = x_284;
x_189 = lean_box(0);
goto block_192;
}
}
}
else
{
lean_object* x_285; 
lean_dec(x_201);
x_285 = lean_ctor_get(x_243, 0);
lean_inc(x_285);
lean_dec_ref(x_243);
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_197;
x_186 = x_198;
x_187 = x_199;
x_188 = x_285;
x_189 = lean_box(0);
goto block_192;
}
}
}
}
else
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_200, 0);
lean_inc(x_290);
lean_dec_ref(x_200);
x_182 = x_193;
x_183 = x_195;
x_184 = x_196;
x_185 = x_197;
x_186 = x_198;
x_187 = x_199;
x_188 = x_290;
x_189 = lean_box(0);
goto block_192;
}
}
block_300:
{
if (x_299 == 0)
{
x_161 = x_296;
x_162 = x_298;
x_163 = x_294;
x_164 = x_297;
x_165 = x_292;
x_166 = x_295;
x_167 = lean_box(0);
goto block_170;
}
else
{
x_193 = x_292;
x_194 = lean_box(0);
x_195 = x_294;
x_196 = x_295;
x_197 = x_296;
x_198 = x_297;
x_199 = x_298;
goto block_291;
}
}
block_311:
{
if (x_309 == 0)
{
lean_dec_ref(x_306);
x_292 = x_301;
x_293 = lean_box(0);
x_294 = x_303;
x_295 = x_304;
x_296 = x_305;
x_297 = x_307;
x_298 = x_308;
x_299 = x_111;
goto block_300;
}
else
{
uint8_t x_310; 
x_310 = l_Lean_Expr_hasFVar(x_306);
lean_dec_ref(x_306);
if (x_310 == 0)
{
x_193 = x_301;
x_194 = lean_box(0);
x_195 = x_303;
x_196 = x_304;
x_197 = x_305;
x_198 = x_307;
x_199 = x_308;
goto block_291;
}
else
{
x_292 = x_301;
x_293 = lean_box(0);
x_294 = x_303;
x_295 = x_304;
x_296 = x_305;
x_297 = x_307;
x_298 = x_308;
x_299 = x_111;
goto block_300;
}
}
}
block_331:
{
lean_object* x_320; 
lean_inc_ref(x_160);
x_320 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_160, x_317);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; uint8_t x_322; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
lean_dec_ref(x_320);
x_322 = l_Lean_Expr_hasMVar(x_321);
if (x_322 == 0)
{
x_301 = x_312;
x_302 = lean_box(0);
x_303 = x_313;
x_304 = x_314;
x_305 = x_315;
x_306 = x_321;
x_307 = x_317;
x_308 = x_318;
x_309 = x_319;
goto block_311;
}
else
{
x_301 = x_312;
x_302 = lean_box(0);
x_303 = x_313;
x_304 = x_314;
x_305 = x_315;
x_306 = x_321;
x_307 = x_317;
x_308 = x_318;
x_309 = x_111;
goto block_311;
}
}
else
{
lean_object* x_323; lean_object* x_324; uint8_t x_325; uint8_t x_330; 
lean_dec(x_317);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_312);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_323 = lean_ctor_get(x_320, 0);
x_330 = !lean_is_exclusive(x_320);
if (x_330 == 0)
{
x_324 = x_320;
x_325 = x_330;
goto block_329;
}
else
{
lean_inc(x_323);
lean_dec(x_320);
x_324 = lean_box(0);
x_325 = x_330;
goto block_329;
}
block_329:
{
lean_object* x_326; 
if (x_325 == 0)
{
x_326 = x_324;
goto block_327;
}
else
{
lean_object* x_328; 
x_328 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_328, 0, x_323);
x_326 = x_328;
goto block_327;
}
block_327:
{
return x_326;
}
}
}
}
block_340:
{
if (x_339 == 0)
{
x_161 = x_335;
x_162 = x_338;
x_163 = x_333;
x_164 = x_337;
x_165 = x_332;
x_166 = x_334;
x_167 = lean_box(0);
goto block_170;
}
else
{
x_312 = x_332;
x_313 = x_333;
x_314 = x_334;
x_315 = x_335;
x_316 = lean_box(0);
x_317 = x_337;
x_318 = x_338;
x_319 = x_339;
goto block_331;
}
}
block_350:
{
uint8_t x_348; 
x_348 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_348 == 0)
{
x_332 = x_345;
x_333 = x_343;
x_334 = x_346;
x_335 = x_341;
x_336 = lean_box(0);
x_337 = x_344;
x_338 = x_342;
x_339 = x_111;
goto block_340;
}
else
{
uint8_t x_349; 
x_349 = l_Lean_Expr_hasFVar(x_160);
if (x_349 == 0)
{
x_312 = x_345;
x_313 = x_343;
x_314 = x_346;
x_315 = x_341;
x_316 = lean_box(0);
x_317 = x_344;
x_318 = x_342;
x_319 = x_348;
goto block_331;
}
else
{
x_332 = x_345;
x_333 = x_343;
x_334 = x_346;
x_335 = x_341;
x_336 = lean_box(0);
x_337 = x_344;
x_338 = x_342;
x_339 = x_111;
goto block_340;
}
}
}
block_414:
{
lean_object* x_359; 
lean_inc(x_357);
lean_inc_ref(x_351);
lean_inc(x_355);
lean_inc_ref(x_358);
x_359 = l_Lean_Meta_isExprDefEq(x_352, x_356, x_358, x_355, x_351, x_357);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; uint8_t x_361; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
lean_dec_ref(x_359);
x_361 = lean_unbox(x_360);
lean_dec(x_360);
if (x_361 == 0)
{
x_341 = x_353;
x_342 = x_12;
x_343 = x_358;
x_344 = x_355;
x_345 = x_351;
x_346 = x_357;
x_347 = lean_box(0);
goto block_350;
}
else
{
lean_object* x_362; 
lean_dec_ref(x_160);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_362 = l_Lean_MVarId_getType(x_2, x_358, x_355, x_351, x_357);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec_ref(x_362);
x_364 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_357);
lean_inc_ref(x_351);
lean_inc(x_355);
lean_inc_ref(x_358);
x_365 = l_Lean_Meta_mkEqOfHEq(x_364, x_12, x_358, x_355, x_351, x_357);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
lean_dec_ref(x_365);
lean_inc(x_355);
x_367 = l_Lean_Meta_mkNoConfusion(x_363, x_366, x_358, x_355, x_351, x_357);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
lean_dec_ref(x_367);
x_369 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_368, x_355);
lean_dec(x_355);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec_ref(x_369);
x_370 = lean_box(x_12);
x_371 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_371, 0, x_370);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_37);
x_373 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_373, 0, x_372);
x_17 = x_373;
x_18 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_374; lean_object* x_375; uint8_t x_376; uint8_t x_381; 
lean_del_object(x_15);
lean_dec(x_14);
x_374 = lean_ctor_get(x_369, 0);
x_381 = !lean_is_exclusive(x_369);
if (x_381 == 0)
{
x_375 = x_369;
x_376 = x_381;
goto block_380;
}
else
{
lean_inc(x_374);
lean_dec(x_369);
x_375 = lean_box(0);
x_376 = x_381;
goto block_380;
}
block_380:
{
lean_object* x_377; 
if (x_376 == 0)
{
x_377 = x_375;
goto block_378;
}
else
{
lean_object* x_379; 
x_379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_379, 0, x_374);
x_377 = x_379;
goto block_378;
}
block_378:
{
return x_377;
}
}
}
}
else
{
lean_object* x_382; lean_object* x_383; uint8_t x_384; uint8_t x_389; 
lean_dec(x_355);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_382 = lean_ctor_get(x_367, 0);
x_389 = !lean_is_exclusive(x_367);
if (x_389 == 0)
{
x_383 = x_367;
x_384 = x_389;
goto block_388;
}
else
{
lean_inc(x_382);
lean_dec(x_367);
x_383 = lean_box(0);
x_384 = x_389;
goto block_388;
}
block_388:
{
lean_object* x_385; 
if (x_384 == 0)
{
x_385 = x_383;
goto block_386;
}
else
{
lean_object* x_387; 
x_387 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_387, 0, x_382);
x_385 = x_387;
goto block_386;
}
block_386:
{
return x_385;
}
}
}
}
else
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; uint8_t x_397; 
lean_dec(x_363);
lean_dec_ref(x_358);
lean_dec(x_357);
lean_dec(x_355);
lean_dec_ref(x_351);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_390 = lean_ctor_get(x_365, 0);
x_397 = !lean_is_exclusive(x_365);
if (x_397 == 0)
{
x_391 = x_365;
x_392 = x_397;
goto block_396;
}
else
{
lean_inc(x_390);
lean_dec(x_365);
x_391 = lean_box(0);
x_392 = x_397;
goto block_396;
}
block_396:
{
lean_object* x_393; 
if (x_392 == 0)
{
x_393 = x_391;
goto block_394;
}
else
{
lean_object* x_395; 
x_395 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_395, 0, x_390);
x_393 = x_395;
goto block_394;
}
block_394:
{
return x_393;
}
}
}
}
else
{
lean_object* x_398; lean_object* x_399; uint8_t x_400; uint8_t x_405; 
lean_dec_ref(x_358);
lean_dec(x_357);
lean_dec(x_355);
lean_dec_ref(x_351);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_398 = lean_ctor_get(x_362, 0);
x_405 = !lean_is_exclusive(x_362);
if (x_405 == 0)
{
x_399 = x_362;
x_400 = x_405;
goto block_404;
}
else
{
lean_inc(x_398);
lean_dec(x_362);
x_399 = lean_box(0);
x_400 = x_405;
goto block_404;
}
block_404:
{
lean_object* x_401; 
if (x_400 == 0)
{
x_401 = x_399;
goto block_402;
}
else
{
lean_object* x_403; 
x_403 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_403, 0, x_398);
x_401 = x_403;
goto block_402;
}
block_402:
{
return x_401;
}
}
}
}
}
else
{
lean_object* x_406; lean_object* x_407; uint8_t x_408; uint8_t x_413; 
lean_dec_ref(x_358);
lean_dec(x_357);
lean_dec(x_355);
lean_dec_ref(x_351);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_406 = lean_ctor_get(x_359, 0);
x_413 = !lean_is_exclusive(x_359);
if (x_413 == 0)
{
x_407 = x_359;
x_408 = x_413;
goto block_412;
}
else
{
lean_inc(x_406);
lean_dec(x_359);
x_407 = lean_box(0);
x_408 = x_413;
goto block_412;
}
block_412:
{
lean_object* x_409; 
if (x_408 == 0)
{
x_409 = x_407;
goto block_410;
}
else
{
lean_object* x_411; 
x_411 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_411, 0, x_406);
x_409 = x_411;
goto block_410;
}
block_410:
{
return x_409;
}
}
}
}
block_465:
{
lean_object* x_421; 
lean_inc(x_419);
lean_inc_ref(x_418);
lean_inc(x_417);
lean_inc_ref(x_416);
lean_inc_ref(x_160);
x_421 = l_Lean_Meta_matchHEq_x3f(x_160, x_416, x_417, x_418, x_419);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
lean_dec_ref(x_421);
if (lean_obj_tag(x_422) == 1)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
lean_dec_ref(x_422);
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_423, 0);
lean_inc(x_426);
lean_dec(x_423);
x_427 = lean_ctor_get(x_424, 0);
lean_inc(x_427);
lean_dec(x_424);
x_428 = lean_ctor_get(x_425, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_425, 1);
lean_inc(x_429);
lean_dec(x_425);
lean_inc(x_419);
lean_inc_ref(x_418);
lean_inc(x_417);
lean_inc_ref(x_416);
x_430 = l_Lean_Meta_matchConstructorApp_x3f(x_427, x_416, x_417, x_418, x_419);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
lean_dec_ref(x_430);
if (lean_obj_tag(x_431) == 1)
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
lean_dec_ref(x_431);
lean_inc(x_419);
lean_inc_ref(x_418);
lean_inc(x_417);
lean_inc_ref(x_416);
x_433 = l_Lean_Meta_matchConstructorApp_x3f(x_429, x_416, x_417, x_418, x_419);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
lean_dec_ref(x_433);
if (lean_obj_tag(x_434) == 1)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; 
x_435 = lean_ctor_get(x_432, 0);
lean_inc_ref(x_435);
lean_dec(x_432);
x_436 = lean_ctor_get(x_434, 0);
lean_inc(x_436);
lean_dec_ref(x_434);
x_437 = lean_ctor_get(x_436, 0);
lean_inc_ref(x_437);
lean_dec(x_436);
x_438 = lean_ctor_get(x_435, 0);
lean_inc(x_438);
lean_dec_ref(x_435);
x_439 = lean_ctor_get(x_437, 0);
lean_inc(x_439);
lean_dec_ref(x_437);
x_440 = lean_name_eq(x_438, x_439);
lean_dec(x_439);
lean_dec(x_438);
if (x_440 == 0)
{
x_351 = x_418;
x_352 = x_426;
x_353 = x_415;
x_354 = lean_box(0);
x_355 = x_417;
x_356 = x_428;
x_357 = x_419;
x_358 = x_416;
goto block_414;
}
else
{
if (x_111 == 0)
{
lean_dec(x_428);
lean_dec(x_426);
x_341 = x_415;
x_342 = x_12;
x_343 = x_416;
x_344 = x_417;
x_345 = x_418;
x_346 = x_419;
x_347 = lean_box(0);
goto block_350;
}
else
{
x_351 = x_418;
x_352 = x_426;
x_353 = x_415;
x_354 = lean_box(0);
x_355 = x_417;
x_356 = x_428;
x_357 = x_419;
x_358 = x_416;
goto block_414;
}
}
}
else
{
lean_dec(x_434);
lean_dec(x_432);
lean_dec(x_428);
lean_dec(x_426);
x_341 = x_415;
x_342 = x_12;
x_343 = x_416;
x_344 = x_417;
x_345 = x_418;
x_346 = x_419;
x_347 = lean_box(0);
goto block_350;
}
}
else
{
lean_object* x_441; lean_object* x_442; uint8_t x_443; uint8_t x_448; 
lean_dec(x_432);
lean_dec(x_428);
lean_dec(x_426);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_441 = lean_ctor_get(x_433, 0);
x_448 = !lean_is_exclusive(x_433);
if (x_448 == 0)
{
x_442 = x_433;
x_443 = x_448;
goto block_447;
}
else
{
lean_inc(x_441);
lean_dec(x_433);
x_442 = lean_box(0);
x_443 = x_448;
goto block_447;
}
block_447:
{
lean_object* x_444; 
if (x_443 == 0)
{
x_444 = x_442;
goto block_445;
}
else
{
lean_object* x_446; 
x_446 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_446, 0, x_441);
x_444 = x_446;
goto block_445;
}
block_445:
{
return x_444;
}
}
}
}
else
{
lean_dec(x_431);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_426);
x_341 = x_415;
x_342 = x_12;
x_343 = x_416;
x_344 = x_417;
x_345 = x_418;
x_346 = x_419;
x_347 = lean_box(0);
goto block_350;
}
}
else
{
lean_object* x_449; lean_object* x_450; uint8_t x_451; uint8_t x_456; 
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_426);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_449 = lean_ctor_get(x_430, 0);
x_456 = !lean_is_exclusive(x_430);
if (x_456 == 0)
{
x_450 = x_430;
x_451 = x_456;
goto block_455;
}
else
{
lean_inc(x_449);
lean_dec(x_430);
x_450 = lean_box(0);
x_451 = x_456;
goto block_455;
}
block_455:
{
lean_object* x_452; 
if (x_451 == 0)
{
x_452 = x_450;
goto block_453;
}
else
{
lean_object* x_454; 
x_454 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_454, 0, x_449);
x_452 = x_454;
goto block_453;
}
block_453:
{
return x_452;
}
}
}
}
else
{
lean_dec(x_422);
x_341 = x_415;
x_342 = x_111;
x_343 = x_416;
x_344 = x_417;
x_345 = x_418;
x_346 = x_419;
x_347 = lean_box(0);
goto block_350;
}
}
else
{
lean_object* x_457; lean_object* x_458; uint8_t x_459; uint8_t x_464; 
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec_ref(x_416);
lean_dec_ref(x_160);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_457 = lean_ctor_get(x_421, 0);
x_464 = !lean_is_exclusive(x_421);
if (x_464 == 0)
{
x_458 = x_421;
x_459 = x_464;
goto block_463;
}
else
{
lean_inc(x_457);
lean_dec(x_421);
x_458 = lean_box(0);
x_459 = x_464;
goto block_463;
}
block_463:
{
lean_object* x_460; 
if (x_459 == 0)
{
x_460 = x_458;
goto block_461;
}
else
{
lean_object* x_462; 
x_462 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_462, 0, x_457);
x_460 = x_462;
goto block_461;
}
block_461:
{
return x_460;
}
}
}
}
block_512:
{
lean_object* x_471; 
lean_inc(x_469);
lean_inc_ref(x_468);
lean_inc(x_467);
lean_inc_ref(x_466);
lean_inc_ref(x_160);
x_471 = l_Lean_Meta_matchEq_x3f(x_160, x_466, x_467, x_468, x_469);
if (lean_obj_tag(x_471) == 0)
{
lean_object* x_472; 
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
lean_dec_ref(x_471);
if (lean_obj_tag(x_472) == 1)
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_473 = lean_ctor_get(x_472, 0);
lean_inc(x_473);
lean_dec_ref(x_472);
x_474 = lean_ctor_get(x_473, 1);
lean_inc(x_474);
lean_dec(x_473);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec(x_474);
lean_inc(x_469);
lean_inc_ref(x_468);
lean_inc(x_467);
lean_inc_ref(x_466);
x_477 = l_Lean_Meta_matchConstructorApp_x3f(x_475, x_466, x_467, x_468, x_469);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
lean_dec_ref(x_477);
if (lean_obj_tag(x_478) == 1)
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
lean_dec_ref(x_478);
lean_inc(x_469);
lean_inc_ref(x_468);
lean_inc(x_467);
lean_inc_ref(x_466);
x_480 = l_Lean_Meta_matchConstructorApp_x3f(x_476, x_466, x_467, x_468, x_469);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
lean_dec_ref(x_480);
if (lean_obj_tag(x_481) == 1)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
x_482 = lean_ctor_get(x_479, 0);
lean_inc_ref(x_482);
lean_dec(x_479);
x_483 = lean_ctor_get(x_481, 0);
lean_inc(x_483);
lean_dec_ref(x_481);
x_484 = lean_ctor_get(x_483, 0);
lean_inc_ref(x_484);
lean_dec(x_483);
x_485 = lean_ctor_get(x_482, 0);
lean_inc(x_485);
lean_dec_ref(x_482);
x_486 = lean_ctor_get(x_484, 0);
lean_inc(x_486);
lean_dec_ref(x_484);
x_487 = lean_name_eq(x_485, x_486);
lean_dec(x_486);
lean_dec(x_485);
if (x_487 == 0)
{
lean_dec_ref(x_160);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_38 = lean_box(0);
x_39 = x_466;
x_40 = x_467;
x_41 = x_469;
x_42 = x_468;
goto block_79;
}
else
{
if (x_111 == 0)
{
lean_del_object(x_35);
x_415 = x_12;
x_416 = x_466;
x_417 = x_467;
x_418 = x_468;
x_419 = x_469;
x_420 = lean_box(0);
goto block_465;
}
else
{
lean_dec_ref(x_160);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_38 = lean_box(0);
x_39 = x_466;
x_40 = x_467;
x_41 = x_469;
x_42 = x_468;
goto block_79;
}
}
}
else
{
lean_dec(x_481);
lean_dec(x_479);
lean_del_object(x_35);
x_415 = x_12;
x_416 = x_466;
x_417 = x_467;
x_418 = x_468;
x_419 = x_469;
x_420 = lean_box(0);
goto block_465;
}
}
else
{
lean_object* x_488; lean_object* x_489; uint8_t x_490; uint8_t x_495; 
lean_dec(x_479);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_488 = lean_ctor_get(x_480, 0);
x_495 = !lean_is_exclusive(x_480);
if (x_495 == 0)
{
x_489 = x_480;
x_490 = x_495;
goto block_494;
}
else
{
lean_inc(x_488);
lean_dec(x_480);
x_489 = lean_box(0);
x_490 = x_495;
goto block_494;
}
block_494:
{
lean_object* x_491; 
if (x_490 == 0)
{
x_491 = x_489;
goto block_492;
}
else
{
lean_object* x_493; 
x_493 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_493, 0, x_488);
x_491 = x_493;
goto block_492;
}
block_492:
{
return x_491;
}
}
}
}
else
{
lean_dec(x_478);
lean_dec(x_476);
lean_del_object(x_35);
x_415 = x_12;
x_416 = x_466;
x_417 = x_467;
x_418 = x_468;
x_419 = x_469;
x_420 = lean_box(0);
goto block_465;
}
}
else
{
lean_object* x_496; lean_object* x_497; uint8_t x_498; uint8_t x_503; 
lean_dec(x_476);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_496 = lean_ctor_get(x_477, 0);
x_503 = !lean_is_exclusive(x_477);
if (x_503 == 0)
{
x_497 = x_477;
x_498 = x_503;
goto block_502;
}
else
{
lean_inc(x_496);
lean_dec(x_477);
x_497 = lean_box(0);
x_498 = x_503;
goto block_502;
}
block_502:
{
lean_object* x_499; 
if (x_498 == 0)
{
x_499 = x_497;
goto block_500;
}
else
{
lean_object* x_501; 
x_501 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_501, 0, x_496);
x_499 = x_501;
goto block_500;
}
block_500:
{
return x_499;
}
}
}
}
else
{
lean_dec(x_472);
lean_del_object(x_35);
x_415 = x_111;
x_416 = x_466;
x_417 = x_467;
x_418 = x_468;
x_419 = x_469;
x_420 = lean_box(0);
goto block_465;
}
}
else
{
lean_object* x_504; lean_object* x_505; uint8_t x_506; uint8_t x_511; 
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_504 = lean_ctor_get(x_471, 0);
x_511 = !lean_is_exclusive(x_471);
if (x_511 == 0)
{
x_505 = x_471;
x_506 = x_511;
goto block_510;
}
else
{
lean_inc(x_504);
lean_dec(x_471);
x_505 = lean_box(0);
x_506 = x_511;
goto block_510;
}
block_510:
{
lean_object* x_507; 
if (x_506 == 0)
{
x_507 = x_505;
goto block_508;
}
else
{
lean_object* x_509; 
x_509 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_509, 0, x_504);
x_507 = x_509;
goto block_508;
}
block_508:
{
return x_507;
}
}
}
}
block_650:
{
lean_object* x_518; 
lean_inc(x_516);
lean_inc_ref(x_515);
lean_inc(x_514);
lean_inc_ref(x_513);
lean_inc_ref(x_160);
x_518 = l_refutableHasNotBit_x3f(x_160, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
lean_dec_ref(x_518);
if (lean_obj_tag(x_519) == 1)
{
lean_object* x_520; lean_object* x_521; uint8_t x_522; uint8_t x_560; 
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_520 = lean_ctor_get(x_519, 0);
x_560 = !lean_is_exclusive(x_519);
if (x_560 == 0)
{
x_521 = x_519;
x_522 = x_560;
goto block_559;
}
else
{
lean_inc(x_520);
lean_dec(x_519);
x_521 = lean_box(0);
x_522 = x_560;
goto block_559;
}
block_559:
{
lean_object* x_523; 
lean_inc(x_2);
x_523 = l_Lean_MVarId_getType(x_2, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
lean_dec_ref(x_523);
x_525 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_514);
x_526 = l_Lean_Meta_mkAbsurd(x_524, x_520, x_525, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; 
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
lean_dec_ref(x_526);
x_528 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_527, x_514);
lean_dec(x_514);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; 
lean_dec_ref(x_528);
x_529 = lean_box(x_12);
if (x_522 == 0)
{
lean_ctor_set(x_521, 0, x_529);
x_530 = x_521;
goto block_533;
}
else
{
lean_object* x_534; 
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_529);
x_530 = x_534;
goto block_533;
}
block_533:
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_37);
x_532 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_532, 0, x_531);
x_17 = x_532;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_535; lean_object* x_536; uint8_t x_537; uint8_t x_542; 
lean_del_object(x_521);
lean_del_object(x_15);
lean_dec(x_14);
x_535 = lean_ctor_get(x_528, 0);
x_542 = !lean_is_exclusive(x_528);
if (x_542 == 0)
{
x_536 = x_528;
x_537 = x_542;
goto block_541;
}
else
{
lean_inc(x_535);
lean_dec(x_528);
x_536 = lean_box(0);
x_537 = x_542;
goto block_541;
}
block_541:
{
lean_object* x_538; 
if (x_537 == 0)
{
x_538 = x_536;
goto block_539;
}
else
{
lean_object* x_540; 
x_540 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_540, 0, x_535);
x_538 = x_540;
goto block_539;
}
block_539:
{
return x_538;
}
}
}
}
else
{
lean_object* x_543; lean_object* x_544; uint8_t x_545; uint8_t x_550; 
lean_del_object(x_521);
lean_dec(x_514);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_543 = lean_ctor_get(x_526, 0);
x_550 = !lean_is_exclusive(x_526);
if (x_550 == 0)
{
x_544 = x_526;
x_545 = x_550;
goto block_549;
}
else
{
lean_inc(x_543);
lean_dec(x_526);
x_544 = lean_box(0);
x_545 = x_550;
goto block_549;
}
block_549:
{
lean_object* x_546; 
if (x_545 == 0)
{
x_546 = x_544;
goto block_547;
}
else
{
lean_object* x_548; 
x_548 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_548, 0, x_543);
x_546 = x_548;
goto block_547;
}
block_547:
{
return x_546;
}
}
}
}
else
{
lean_object* x_551; lean_object* x_552; uint8_t x_553; uint8_t x_558; 
lean_del_object(x_521);
lean_dec(x_520);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_551 = lean_ctor_get(x_523, 0);
x_558 = !lean_is_exclusive(x_523);
if (x_558 == 0)
{
x_552 = x_523;
x_553 = x_558;
goto block_557;
}
else
{
lean_inc(x_551);
lean_dec(x_523);
x_552 = lean_box(0);
x_553 = x_558;
goto block_557;
}
block_557:
{
lean_object* x_554; 
if (x_553 == 0)
{
x_554 = x_552;
goto block_555;
}
else
{
lean_object* x_556; 
x_556 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_556, 0, x_551);
x_554 = x_556;
goto block_555;
}
block_555:
{
return x_554;
}
}
}
}
}
else
{
lean_object* x_561; 
lean_dec(x_519);
lean_inc(x_516);
lean_inc_ref(x_515);
lean_inc(x_514);
lean_inc_ref(x_513);
lean_inc_ref(x_160);
x_561 = l_Lean_Meta_matchNe_x3f(x_160, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
lean_dec_ref(x_561);
if (lean_obj_tag(x_562) == 1)
{
lean_object* x_563; lean_object* x_564; uint8_t x_565; uint8_t x_633; 
x_563 = lean_ctor_get(x_562, 0);
x_633 = !lean_is_exclusive(x_562);
if (x_633 == 0)
{
x_564 = x_562;
x_565 = x_633;
goto block_632;
}
else
{
lean_inc(x_563);
lean_dec(x_562);
x_564 = lean_box(0);
x_565 = x_633;
goto block_632;
}
block_632:
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; uint8_t x_631; 
x_566 = lean_ctor_get(x_563, 1);
lean_inc(x_566);
lean_dec(x_563);
x_567 = lean_ctor_get(x_566, 0);
x_568 = lean_ctor_get(x_566, 1);
x_631 = !lean_is_exclusive(x_566);
if (x_631 == 0)
{
x_569 = x_566;
x_570 = x_631;
goto block_630;
}
else
{
lean_inc(x_568);
lean_inc(x_567);
lean_dec(x_566);
x_569 = lean_box(0);
x_570 = x_631;
goto block_630;
}
block_630:
{
lean_object* x_571; 
lean_inc(x_516);
lean_inc_ref(x_515);
lean_inc(x_514);
lean_inc_ref(x_513);
lean_inc(x_567);
x_571 = l_Lean_Meta_isExprDefEq(x_567, x_568, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; uint8_t x_573; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec_ref(x_571);
x_573 = lean_unbox(x_572);
lean_dec(x_572);
if (x_573 == 0)
{
lean_del_object(x_569);
lean_dec(x_567);
lean_del_object(x_564);
x_466 = x_513;
x_467 = x_514;
x_468 = x_515;
x_469 = x_516;
x_470 = lean_box(0);
goto block_512;
}
else
{
lean_object* x_574; 
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_574 = l_Lean_MVarId_getType(x_2, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
lean_dec_ref(x_574);
lean_inc(x_516);
lean_inc_ref(x_515);
lean_inc(x_514);
lean_inc_ref(x_513);
x_576 = l_Lean_Meta_mkEqRefl(x_567, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
lean_dec_ref(x_576);
x_578 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_514);
x_579 = l_Lean_Meta_mkAbsurd(x_575, x_577, x_578, x_513, x_514, x_515, x_516);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
lean_dec_ref(x_579);
x_581 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_580, x_514);
lean_dec(x_514);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; 
lean_dec_ref(x_581);
x_582 = lean_box(x_12);
if (x_565 == 0)
{
lean_ctor_set(x_564, 0, x_582);
x_583 = x_564;
goto block_588;
}
else
{
lean_object* x_589; 
x_589 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_589, 0, x_582);
x_583 = x_589;
goto block_588;
}
block_588:
{
lean_object* x_584; 
if (x_570 == 0)
{
lean_ctor_set(x_569, 1, x_37);
lean_ctor_set(x_569, 0, x_583);
x_584 = x_569;
goto block_586;
}
else
{
lean_object* x_587; 
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_583);
lean_ctor_set(x_587, 1, x_37);
x_584 = x_587;
goto block_586;
}
block_586:
{
lean_object* x_585; 
x_585 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_585, 0, x_584);
x_17 = x_585;
x_18 = lean_box(0);
goto block_24;
}
}
}
else
{
lean_object* x_590; lean_object* x_591; uint8_t x_592; uint8_t x_597; 
lean_del_object(x_569);
lean_del_object(x_564);
lean_del_object(x_15);
lean_dec(x_14);
x_590 = lean_ctor_get(x_581, 0);
x_597 = !lean_is_exclusive(x_581);
if (x_597 == 0)
{
x_591 = x_581;
x_592 = x_597;
goto block_596;
}
else
{
lean_inc(x_590);
lean_dec(x_581);
x_591 = lean_box(0);
x_592 = x_597;
goto block_596;
}
block_596:
{
lean_object* x_593; 
if (x_592 == 0)
{
x_593 = x_591;
goto block_594;
}
else
{
lean_object* x_595; 
x_595 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_595, 0, x_590);
x_593 = x_595;
goto block_594;
}
block_594:
{
return x_593;
}
}
}
}
else
{
lean_object* x_598; lean_object* x_599; uint8_t x_600; uint8_t x_605; 
lean_del_object(x_569);
lean_del_object(x_564);
lean_dec(x_514);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_598 = lean_ctor_get(x_579, 0);
x_605 = !lean_is_exclusive(x_579);
if (x_605 == 0)
{
x_599 = x_579;
x_600 = x_605;
goto block_604;
}
else
{
lean_inc(x_598);
lean_dec(x_579);
x_599 = lean_box(0);
x_600 = x_605;
goto block_604;
}
block_604:
{
lean_object* x_601; 
if (x_600 == 0)
{
x_601 = x_599;
goto block_602;
}
else
{
lean_object* x_603; 
x_603 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_603, 0, x_598);
x_601 = x_603;
goto block_602;
}
block_602:
{
return x_601;
}
}
}
}
else
{
lean_object* x_606; lean_object* x_607; uint8_t x_608; uint8_t x_613; 
lean_dec(x_575);
lean_del_object(x_569);
lean_del_object(x_564);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_606 = lean_ctor_get(x_576, 0);
x_613 = !lean_is_exclusive(x_576);
if (x_613 == 0)
{
x_607 = x_576;
x_608 = x_613;
goto block_612;
}
else
{
lean_inc(x_606);
lean_dec(x_576);
x_607 = lean_box(0);
x_608 = x_613;
goto block_612;
}
block_612:
{
lean_object* x_609; 
if (x_608 == 0)
{
x_609 = x_607;
goto block_610;
}
else
{
lean_object* x_611; 
x_611 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_611, 0, x_606);
x_609 = x_611;
goto block_610;
}
block_610:
{
return x_609;
}
}
}
}
else
{
lean_object* x_614; lean_object* x_615; uint8_t x_616; uint8_t x_621; 
lean_del_object(x_569);
lean_dec(x_567);
lean_del_object(x_564);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_614 = lean_ctor_get(x_574, 0);
x_621 = !lean_is_exclusive(x_574);
if (x_621 == 0)
{
x_615 = x_574;
x_616 = x_621;
goto block_620;
}
else
{
lean_inc(x_614);
lean_dec(x_574);
x_615 = lean_box(0);
x_616 = x_621;
goto block_620;
}
block_620:
{
lean_object* x_617; 
if (x_616 == 0)
{
x_617 = x_615;
goto block_618;
}
else
{
lean_object* x_619; 
x_619 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_619, 0, x_614);
x_617 = x_619;
goto block_618;
}
block_618:
{
return x_617;
}
}
}
}
}
else
{
lean_object* x_622; lean_object* x_623; uint8_t x_624; uint8_t x_629; 
lean_del_object(x_569);
lean_dec(x_567);
lean_del_object(x_564);
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_622 = lean_ctor_get(x_571, 0);
x_629 = !lean_is_exclusive(x_571);
if (x_629 == 0)
{
x_623 = x_571;
x_624 = x_629;
goto block_628;
}
else
{
lean_inc(x_622);
lean_dec(x_571);
x_623 = lean_box(0);
x_624 = x_629;
goto block_628;
}
block_628:
{
lean_object* x_625; 
if (x_624 == 0)
{
x_625 = x_623;
goto block_626;
}
else
{
lean_object* x_627; 
x_627 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_627, 0, x_622);
x_625 = x_627;
goto block_626;
}
block_626:
{
return x_625;
}
}
}
}
}
}
else
{
lean_dec(x_562);
x_466 = x_513;
x_467 = x_514;
x_468 = x_515;
x_469 = x_516;
x_470 = lean_box(0);
goto block_512;
}
}
else
{
lean_object* x_634; lean_object* x_635; uint8_t x_636; uint8_t x_641; 
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_634 = lean_ctor_get(x_561, 0);
x_641 = !lean_is_exclusive(x_561);
if (x_641 == 0)
{
x_635 = x_561;
x_636 = x_641;
goto block_640;
}
else
{
lean_inc(x_634);
lean_dec(x_561);
x_635 = lean_box(0);
x_636 = x_641;
goto block_640;
}
block_640:
{
lean_object* x_637; 
if (x_636 == 0)
{
x_637 = x_635;
goto block_638;
}
else
{
lean_object* x_639; 
x_639 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_639, 0, x_634);
x_637 = x_639;
goto block_638;
}
block_638:
{
return x_637;
}
}
}
}
}
else
{
lean_object* x_642; lean_object* x_643; uint8_t x_644; uint8_t x_649; 
lean_dec(x_516);
lean_dec_ref(x_515);
lean_dec(x_514);
lean_dec_ref(x_513);
lean_dec_ref(x_160);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_642 = lean_ctor_get(x_518, 0);
x_649 = !lean_is_exclusive(x_518);
if (x_649 == 0)
{
x_643 = x_518;
x_644 = x_649;
goto block_648;
}
else
{
lean_inc(x_642);
lean_dec(x_518);
x_643 = lean_box(0);
x_644 = x_649;
goto block_648;
}
block_648:
{
lean_object* x_645; 
if (x_644 == 0)
{
x_645 = x_643;
goto block_646;
}
else
{
lean_object* x_647; 
x_647 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_647, 0, x_642);
x_645 = x_647;
goto block_646;
}
block_646:
{
return x_645;
}
}
}
}
}
else
{
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_80;
x_27 = lean_box(0);
goto block_32;
}
block_79:
{
lean_object* x_43; 
lean_inc(x_2);
x_43 = l_Lean_MVarId_getType(x_2, x_39, x_40, x_42, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_LocalDecl_toExpr(x_34);
lean_inc(x_40);
x_46 = l_Lean_Meta_mkNoConfusion(x_44, x_45, x_39, x_40, x_42, x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_47, x_40);
lean_dec(x_40);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_48);
x_49 = lean_box(x_12);
if (x_36 == 0)
{
lean_ctor_set(x_35, 0, x_49);
x_50 = x_35;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_50 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_37);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_17 = x_52;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_del_object(x_35);
lean_del_object(x_15);
lean_dec(x_14);
x_55 = lean_ctor_get(x_48, 0);
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
x_56 = x_48;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec(x_40);
lean_del_object(x_35);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_63 = lean_ctor_get(x_46, 0);
x_70 = !lean_is_exclusive(x_46);
if (x_70 == 0)
{
x_64 = x_46;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_46);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_del_object(x_35);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_71 = lean_ctor_get(x_43, 0);
x_78 = !lean_is_exclusive(x_43);
if (x_78 == 0)
{
x_72 = x_43;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_43);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
block_103:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_1, 0);
x_87 = l_Lean_LocalDecl_fvarId(x_34);
lean_dec(x_34);
lean_inc(x_86);
lean_inc(x_2);
x_88 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_2, x_87, x_86, x_85, x_83, x_84, x_82);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_80;
x_27 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_91 = lean_box(x_12);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_37);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_17 = x_94;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_102; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = lean_ctor_get(x_88, 0);
x_102 = !lean_is_exclusive(x_88);
if (x_102 == 0)
{
x_96 = x_88;
x_97 = x_102;
goto block_101;
}
else
{
lean_inc(x_95);
lean_dec(x_88);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
block_110:
{
if (x_109 == 0)
{
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
x_26 = x_80;
x_27 = lean_box(0);
goto block_32;
}
else
{
x_81 = lean_box(0);
x_82 = x_106;
x_83 = x_105;
x_84 = x_108;
x_85 = x_107;
goto block_103;
}
}
block_118:
{
if (x_117 == 0)
{
x_81 = lean_box(0);
x_82 = x_114;
x_83 = x_113;
x_84 = x_116;
x_85 = x_115;
goto block_103;
}
else
{
x_104 = lean_box(0);
x_105 = x_113;
x_106 = x_114;
x_107 = x_115;
x_108 = x_116;
x_109 = x_111;
goto block_110;
}
}
block_126:
{
if (x_125 == 0)
{
x_104 = lean_box(0);
x_105 = x_121;
x_106 = x_120;
x_107 = x_123;
x_108 = x_122;
x_109 = x_111;
goto block_110;
}
else
{
x_112 = lean_box(0);
x_113 = x_121;
x_114 = x_120;
x_115 = x_123;
x_116 = x_122;
x_117 = x_124;
goto block_118;
}
}
block_135:
{
uint8_t x_134; 
x_134 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_134 == 0)
{
x_119 = lean_box(0);
x_120 = x_132;
x_121 = x_130;
x_122 = x_131;
x_123 = x_129;
x_124 = x_128;
x_125 = x_111;
goto block_126;
}
else
{
if (x_127 == 0)
{
x_112 = lean_box(0);
x_113 = x_130;
x_114 = x_132;
x_115 = x_129;
x_116 = x_131;
x_117 = x_128;
goto block_118;
}
else
{
x_119 = lean_box(0);
x_120 = x_132;
x_121 = x_130;
x_122 = x_131;
x_123 = x_129;
x_124 = x_128;
x_125 = x_111;
goto block_126;
}
}
}
block_159:
{
if (x_143 == 0)
{
x_127 = x_137;
x_128 = x_141;
x_129 = x_138;
x_130 = x_140;
x_131 = x_136;
x_132 = x_139;
x_133 = lean_box(0);
goto block_135;
}
else
{
lean_object* x_144; 
lean_inc(x_139);
lean_inc_ref(x_136);
lean_inc(x_140);
lean_inc_ref(x_138);
lean_inc(x_34);
lean_inc(x_2);
x_144 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_2, x_34, x_138, x_140, x_136, x_139);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
x_127 = x_137;
x_128 = x_141;
x_129 = x_138;
x_130 = x_140;
x_131 = x_136;
x_132 = x_139;
x_133 = lean_box(0);
goto block_135;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_136);
lean_dec(x_34);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_147 = lean_box(x_12);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_37);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_17 = x_150;
x_18 = lean_box(0);
goto block_24;
}
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_158; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec_ref(x_136);
lean_dec(x_34);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_151 = lean_ctor_get(x_144, 0);
x_158 = !lean_is_exclusive(x_144);
if (x_158 == 0)
{
x_152 = x_144;
x_153 = x_158;
goto block_157;
}
else
{
lean_inc(x_151);
lean_dec(x_144);
x_152 = lean_box(0);
x_153 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_154; 
if (x_153 == 0)
{
x_154 = x_152;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_151);
x_154 = x_156;
goto block_155;
}
block_155:
{
return x_154;
}
}
}
}
}
}
}
block_24:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_19);
x_20 = x_15;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_14);
x_20 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
block_32:
{
lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
x_29 = 1;
x_30 = lean_usize_add(x_5, x_29);
x_31 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_3, x_4, x_30, x_28, x_7, x_8, x_9, x_10);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_45; 
x_11 = lean_ctor_get(x_4, 0);
x_45 = !lean_is_exclusive(x_4);
if (x_45 == 0)
{
x_12 = x_4;
x_13 = x_45;
goto block_44;
}
else
{
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_array_size(x_11);
x_17 = 0;
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_11, x_16, x_17, x_15, x_6, x_7, x_8, x_9);
lean_dec_ref(x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_35; 
x_19 = lean_ctor_get(x_18, 0);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
x_20 = x_18;
x_21 = x_35;
goto block_34;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_23);
x_24 = x_12;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_23);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_24);
x_25 = x_20;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_inc_ref(x_22);
lean_dec(x_19);
lean_del_object(x_12);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec_ref(x_22);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_30);
x_31 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_43; 
lean_del_object(x_12);
x_36 = lean_ctor_get(x_18, 0);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
x_37 = x_18;
x_38 = x_43;
goto block_42;
}
else
{
lean_inc(x_36);
lean_dec(x_18);
x_37 = lean_box(0);
x_38 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_39; 
if (x_38 == 0)
{
x_39 = x_37;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_36);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_80; 
x_46 = lean_ctor_get(x_4, 0);
x_80 = !lean_is_exclusive(x_4);
if (x_80 == 0)
{
x_47 = x_4;
x_48 = x_80;
goto block_79;
}
else
{
lean_inc(x_46);
lean_dec(x_4);
x_47 = lean_box(0);
x_48 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_5);
x_51 = lean_array_size(x_46);
x_52 = 0;
x_53 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(x_1, x_2, x_46, x_51, x_52, x_50, x_6, x_7, x_8, x_9);
lean_dec_ref(x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_70; 
x_54 = lean_ctor_get(x_53, 0);
x_70 = !lean_is_exclusive(x_53);
if (x_70 == 0)
{
x_55 = x_53;
x_56 = x_70;
goto block_69;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_54, 0);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
if (x_48 == 0)
{
lean_ctor_set(x_47, 0, x_58);
x_59 = x_47;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_58);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_59);
x_60 = x_55;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_59);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_inc_ref(x_57);
lean_dec(x_54);
lean_del_object(x_47);
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
lean_dec_ref(x_57);
if (x_56 == 0)
{
lean_ctor_set(x_55, 0, x_65);
x_66 = x_55;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_78; 
lean_del_object(x_47);
x_71 = lean_ctor_get(x_53, 0);
x_78 = !lean_is_exclusive(x_53);
if (x_78 == 0)
{
x_72 = x_53;
x_73 = x_78;
goto block_77;
}
else
{
lean_inc(x_71);
lean_dec(x_53);
x_72 = lean_box(0);
x_73 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_74; 
if (x_73 == 0)
{
x_74 = x_72;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_71);
x_74 = x_76;
goto block_75;
}
block_75:
{
return x_74;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_49; 
x_15 = lean_ctor_get(x_7, 1);
x_49 = !lean_is_exclusive(x_7);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_7, 0);
lean_dec(x_50);
x_16 = x_7;
x_17 = x_49;
goto block_48;
}
else
{
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_uget_borrowed(x_4, x_6);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_15);
lean_inc(x_18);
lean_inc(x_2);
lean_inc_ref(x_1);
x_19 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(x_1, x_2, x_3, x_18, x_15, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_39; 
x_20 = lean_ctor_get(x_19, 0);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
x_21 = x_19;
x_22 = x_39;
goto block_38;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_39;
goto block_38;
}
block_38:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_23);
x_24 = x_16;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_15);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_24);
x_25 = x_21;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_del_object(x_21);
lean_dec(x_15);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec_ref(x_20);
x_31 = lean_box(0);
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_30);
lean_ctor_set(x_16, 0, x_31);
x_32 = x_16;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_30);
x_32 = x_37;
goto block_36;
}
block_36:
{
size_t x_33; size_t x_34; 
x_33 = 1;
x_34 = lean_usize_add(x_6, x_33);
x_6 = x_34;
x_7 = x_32;
goto _start;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_del_object(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
lean_dec_ref(x_1);
x_40 = lean_ctor_get(x_19, 0);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
x_41 = x_19;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_19);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_12 = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(x_1, x_2, x_4, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_49; 
x_13 = lean_ctor_get(x_12, 0);
x_49 = !lean_is_exclusive(x_12);
if (x_49 == 0)
{
x_14 = x_12;
x_15 = x_49;
goto block_48;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_49;
goto block_48;
}
block_48:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec_ref(x_13);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_16);
x_17 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
lean_del_object(x_14);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec_ref(x_13);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_array_size(x_11);
x_24 = 0;
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(x_1, x_2, x_11, x_23, x_24, x_22, x_5, x_6, x_7, x_8);
lean_dec_ref(x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_39; 
x_26 = lean_ctor_get(x_25, 0);
x_39 = !lean_is_exclusive(x_25);
if (x_39 == 0)
{
x_27 = x_25;
x_28 = x_39;
goto block_38;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_26, 0);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_31 = x_27;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_inc_ref(x_29);
lean_dec(x_26);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec_ref(x_29);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_34);
x_35 = x_27;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
x_40 = lean_ctor_get(x_25, 0);
x_47 = !lean_is_exclusive(x_25);
if (x_47 == 0)
{
x_41 = x_25;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_12, 0);
x_57 = !lean_is_exclusive(x_12);
if (x_57 == 0)
{
x_51 = x_12;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_12);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec_ref(x_9);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_10 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(x_1, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_10);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
x_16 = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(x_3, x_1, x_14, x_15, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_29; 
x_17 = lean_ctor_get(x_16, 0);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
x_18 = x_16;
x_19 = x_29;
goto block_28;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_11);
x_21 = x_18;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_11);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec_ref(x_20);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_24);
x_25 = x_18;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
lean_dec(x_11);
x_30 = lean_ctor_get(x_16, 0);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
x_31 = x_16;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_38 = lean_ctor_get(x_9, 0);
x_45 = !lean_is_exclusive(x_9);
if (x_45 == 0)
{
x_39 = x_9;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_9);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_contradictionCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_contradictionCore(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_MVarId_contradictionCore(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_21; 
x_9 = lean_ctor_get(x_8, 0);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
x_10 = x_8;
x_11 = x_21;
goto block_20;
}
else
{
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = x_21;
goto block_20;
}
block_20:
{
uint8_t x_12; 
x_12 = lean_unbox(x_9);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_del_object(x_10);
x_13 = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
x_14 = lean_box(0);
x_15 = l_Lean_Meta_throwTacticEx___redArg(x_13, x_1, x_14, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_16 = lean_box(0);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_16);
x_17 = x_10;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_16);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_22 = lean_ctor_get(x_8, 0);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
x_23 = x_8;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_contradiction(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
x_3 = 0;
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return x_2;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasNotBit(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Assumption(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HasNotBit(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Contradiction(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Contradiction(builtin);
}
#ifdef __cplusplus
}
#endif
