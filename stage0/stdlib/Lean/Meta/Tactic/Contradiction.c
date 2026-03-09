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
lean_object* x_11; 
lean_inc_ref(x_2);
x_11 = l_Lean_FVarId_getType___redArg(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_5);
x_13 = l_Lean_Meta_whnfD(x_12, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_40; 
x_14 = lean_ctor_get(x_13, 0);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
x_15 = x_13;
x_16 = x_40;
goto block_39;
}
else
{
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_17; 
x_17 = l_Lean_Expr_getAppFn(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_st_ref_get(x_5);
lean_dec(x_5);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
lean_dec(x_19);
x_21 = 0;
x_22 = l_Lean_Environment_find_x3f(x_20, x_18, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_del_object(x_15);
goto block_10;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 4);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_List_lengthTR___redArg(x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_nat_dec_lt(x_28, x_25);
lean_dec(x_25);
x_31 = lean_box(x_30);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_31);
x_32 = x_15;
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
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_25);
x_35 = lean_box(x_29);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_35);
x_36 = x_15;
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
lean_dec(x_23);
lean_del_object(x_15);
goto block_10;
}
}
}
else
{
lean_dec_ref(x_17);
lean_del_object(x_15);
lean_dec(x_5);
goto block_10;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_48; 
lean_dec(x_5);
x_41 = lean_ctor_get(x_13, 0);
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
x_42 = x_13;
x_43 = x_48;
goto block_47;
}
else
{
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_box(0);
x_43 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_44; 
if (x_43 == 0)
{
x_44 = x_42;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_49 = lean_ctor_get(x_11, 0);
x_56 = !lean_is_exclusive(x_11);
if (x_56 == 0)
{
x_50 = x_11;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_11);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
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
return x_52;
}
}
}
block_10:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_31; lean_object* x_32; lean_object* x_36; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_36 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_36);
x_39 = l_Lean_Meta_SavedState_restore___redArg(x_9, x_4, x_6);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_39, 0);
lean_dec(x_47);
x_40 = x_39;
x_41 = x_46;
goto block_45;
}
else
{
lean_dec(x_39);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_37);
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_37);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_37);
x_48 = lean_ctor_get(x_39, 0);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
x_49 = x_39;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
lean_inc(x_48);
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
x_31 = x_51;
x_32 = x_48;
goto block_35;
}
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_36;
}
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_36, 0);
lean_inc(x_56);
x_31 = x_36;
x_32 = x_56;
goto block_35;
}
block_30:
{
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec_ref(x_11);
x_13 = l_Lean_Meta_SavedState_restore___redArg(x_9, x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_9);
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
lean_ctor_set(x_14, 0, x_10);
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_10);
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
lean_dec_ref(x_10);
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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_11;
}
}
block_35:
{
uint8_t x_33; 
x_33 = l_Lean_Exception_isInterrupt(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_inc_ref(x_32);
x_34 = l_Lean_Exception_isRuntime(x_32);
x_10 = x_32;
x_11 = x_31;
x_12 = x_34;
goto block_30;
}
else
{
x_10 = x_32;
x_11 = x_31;
x_12 = x_33;
goto block_30;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = lean_ctor_get(x_8, 0);
x_64 = !lean_is_exclusive(x_8);
if (x_64 == 0)
{
x_58 = x_8;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_8);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_48; lean_object* x_49; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_48 = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
x_49 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(x_48, x_10);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_72; 
x_50 = lean_ctor_get(x_49, 0);
x_72 = !lean_is_exclusive(x_49);
if (x_72 == 0)
{
x_51 = x_49;
x_52 = x_72;
goto block_71;
}
else
{
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_box(0);
x_52 = x_72;
goto block_71;
}
block_71:
{
uint8_t x_53; 
x_53 = lean_unbox(x_50);
lean_dec(x_50);
if (x_53 == 0)
{
lean_del_object(x_51);
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
goto block_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
x_55 = lean_array_get_size(x_14);
x_56 = l_Nat_reprFast(x_55);
if (x_52 == 0)
{
lean_ctor_set_tag(x_51, 3);
lean_ctor_set(x_51, 0, x_56);
x_57 = x_51;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_56);
x_57 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = l_Lean_MessageData_ofFormat(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_48, x_59, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_60) == 0)
{
lean_dec_ref(x_60);
x_15 = x_7;
x_16 = x_8;
x_17 = x_9;
x_18 = x_10;
x_19 = x_11;
goto block_47;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
x_61 = lean_ctor_get(x_60, 0);
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
x_62 = x_60;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_60);
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
return x_49;
}
block_47:
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
x_21 = lean_array_size(x_14);
x_22 = 0;
x_23 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(x_6, x_14, x_21, x_22, x_20, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_38; 
x_24 = lean_ctor_get(x_23, 0);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
x_25 = x_23;
x_26 = x_38;
goto block_37;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = 1;
x_29 = lean_box(x_28);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_29);
x_30 = x_25;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec_ref(x_27);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_33);
x_34 = x_25;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
x_39 = lean_ctor_get(x_23, 0);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
x_40 = x_23;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_115; 
lean_dec(x_7);
x_73 = lean_ctor_get(x_13, 0);
x_115 = !lean_is_exclusive(x_13);
if (x_115 == 0)
{
x_74 = x_13;
x_75 = x_115;
goto block_114;
}
else
{
lean_inc(x_73);
lean_dec(x_13);
x_74 = lean_box(0);
x_75 = x_115;
goto block_114;
}
block_114:
{
uint8_t x_76; uint8_t x_112; 
x_112 = l_Lean_Exception_isInterrupt(x_73);
if (x_112 == 0)
{
uint8_t x_113; 
lean_inc(x_73);
x_113 = l_Lean_Exception_isRuntime(x_73);
x_76 = x_113;
goto block_111;
}
else
{
x_76 = x_112;
goto block_111;
}
block_111:
{
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_del_object(x_74);
x_77 = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
x_78 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(x_77, x_10);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; uint8_t x_107; 
x_79 = lean_ctor_get(x_78, 0);
x_107 = !lean_is_exclusive(x_78);
if (x_107 == 0)
{
x_80 = x_78;
x_81 = x_107;
goto block_106;
}
else
{
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_box(0);
x_81 = x_107;
goto block_106;
}
block_106:
{
uint8_t x_82; 
x_82 = lean_unbox(x_79);
lean_dec(x_79);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_73);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_83 = lean_box(x_4);
if (x_81 == 0)
{
lean_ctor_set(x_80, 0, x_83);
x_84 = x_80;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_83);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_del_object(x_80);
x_87 = l_Lean_Exception_toMessageData(x_73);
x_88 = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_77, x_87, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; uint8_t x_96; 
x_96 = !lean_is_exclusive(x_88);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_88, 0);
lean_dec(x_97);
x_89 = x_88;
x_90 = x_96;
goto block_95;
}
else
{
lean_dec(x_88);
x_89 = lean_box(0);
x_90 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_box(x_4);
if (x_90 == 0)
{
lean_ctor_set(x_89, 0, x_91);
x_92 = x_89;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_91);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_105; 
x_98 = lean_ctor_get(x_88, 0);
x_105 = !lean_is_exclusive(x_88);
if (x_105 == 0)
{
x_99 = x_88;
x_100 = x_105;
goto block_104;
}
else
{
lean_inc(x_98);
lean_dec(x_88);
x_99 = lean_box(0);
x_100 = x_105;
goto block_104;
}
block_104:
{
lean_object* x_101; 
if (x_100 == 0)
{
x_101 = x_99;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_98);
x_101 = x_103;
goto block_102;
}
block_102:
{
return x_101;
}
}
}
}
}
}
else
{
lean_dec(x_73);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
return x_78;
}
}
else
{
lean_object* x_108; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (x_75 == 0)
{
x_108 = x_74;
goto block_109;
}
else
{
lean_object* x_110; 
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_73);
x_108 = x_110;
goto block_109;
}
block_109:
{
return x_108;
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_st_ref_get(x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_st_ref_take(x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = lean_st_ref_set(x_3, x_18);
x_20 = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
x_21 = lean_box(0);
x_22 = lean_box(x_15);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 12, 6);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_20);
lean_closure_set(x_23, 3, x_22);
lean_closure_set(x_23, 4, x_21);
lean_closure_set(x_23, 5, x_13);
x_24 = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__5(x_23, x_3, x_4, x_5, x_6, x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
x_26 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(x_25, x_6);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
goto block_12;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__6, &l_Lean_Meta_ElimEmptyInductive_elim___closed__6_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__6);
x_30 = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___redArg(x_25, x_29, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_30) == 0)
{
lean_dec_ref(x_30);
goto block_12;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_38; 
x_31 = lean_ctor_get(x_30, 0);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
x_32 = x_30;
x_33 = x_38;
goto block_37;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_34; 
if (x_33 == 0)
{
x_34 = x_32;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_31);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
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
return x_26;
}
}
block_12:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_5, x_4);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec_ref(x_6);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_box(0);
x_22 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
x_23 = lean_array_uget_borrowed(x_3, x_5);
lean_inc(x_20);
x_24 = l_Lean_Meta_FVarSubst_apply(x_20, x_23);
x_25 = l_Lean_Expr_isFVar(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
x_13 = x_22;
goto block_17;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Expr_fvarId_x21(x_24);
lean_dec_ref(x_24);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_26);
x_27 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(x_26, x_8, x_9, x_10, x_11);
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
lean_dec(x_26);
x_13 = x_22;
goto block_17;
}
else
{
lean_object* x_30; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_30 = l_Lean_Meta_ElimEmptyInductive_elim(x_2, x_26, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_41; 
x_31 = lean_ctor_get(x_30, 0);
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
x_32 = x_30;
x_33 = x_41;
goto block_40;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_41;
goto block_40;
}
block_40:
{
uint8_t x_34; 
x_34 = lean_unbox(x_31);
if (x_34 == 0)
{
lean_del_object(x_32);
lean_dec(x_31);
x_13 = x_22;
goto block_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_21);
if (x_33 == 0)
{
lean_ctor_set(x_32, 0, x_36);
x_37 = x_32;
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
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_42 = lean_ctor_get(x_30, 0);
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
x_43 = x_30;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_30);
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
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_26);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_27, 0);
x_57 = !lean_is_exclusive(x_27);
if (x_57 == 0)
{
x_51 = x_27;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_27);
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
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_30; lean_object* x_31; lean_object* x_35; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_35 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec_ref(x_35);
x_38 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_39 = x_38;
x_40 = x_45;
goto block_44;
}
else
{
lean_dec(x_38);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_36);
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_36);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec(x_36);
x_47 = lean_ctor_get(x_38, 0);
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
x_48 = x_38;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_38);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
lean_inc(x_47);
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
x_30 = x_50;
x_31 = x_47;
goto block_34;
}
}
}
}
else
{
lean_dec(x_36);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_35;
}
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_35, 0);
lean_inc(x_55);
x_30 = x_35;
x_31 = x_55;
goto block_34;
}
block_29:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
x_12 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_13 = x_12;
x_14 = x_19;
goto block_18;
}
else
{
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_9);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_9);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec_ref(x_9);
x_21 = lean_ctor_get(x_12, 0);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
x_22 = x_12;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
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
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
block_34:
{
uint8_t x_32; 
x_32 = l_Lean_Exception_isInterrupt(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
lean_inc_ref(x_31);
x_33 = l_Lean_Exception_isRuntime(x_31);
x_9 = x_31;
x_10 = x_30;
x_11 = x_33;
goto block_29;
}
else
{
x_9 = x_31;
x_10 = x_30;
x_11 = x_32;
goto block_29;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_7, 0);
x_63 = !lean_is_exclusive(x_7);
if (x_63 == 0)
{
x_57 = x_7;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_7);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_15; lean_object* x_16; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec_ref(x_1);
x_25 = l_Lean_Level_hasMVar(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
x_1 = x_24;
goto _start;
}
}
case 2:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec_ref(x_1);
x_15 = x_29;
x_16 = x_30;
goto block_23;
}
case 3:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec_ref(x_1);
x_15 = x_31;
x_16 = x_32;
goto block_23;
}
case 5:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec_ref(x_1);
x_34 = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4_spec__6(x_33, x_2, x_3, x_4, x_5);
return x_34;
}
default: 
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
block_14:
{
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec_ref(x_8);
x_10 = l_Lean_Level_hasMVar(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
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
block_23:
{
uint8_t x_17; 
x_17 = l_Lean_Level_hasMVar(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_7 = x_16;
x_8 = x_19;
x_9 = x_17;
goto block_14;
}
else
{
lean_object* x_20; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(x_15, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
x_7 = x_16;
x_8 = x_20;
x_9 = x_22;
goto block_14;
}
else
{
lean_dec(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_20;
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_15; lean_object* x_16; 
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec_ref(x_1);
x_25 = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__3___redArg(x_24, x_3);
lean_dec(x_3);
return x_25;
}
case 3:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec_ref(x_1);
x_27 = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__4(x_26, x_2, x_3, x_4, x_5);
return x_27;
}
case 4:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec_ref(x_1);
x_29 = l_List_anyM___at___00Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3_spec__5(x_28, x_2, x_3, x_4, x_5);
return x_29;
}
case 5:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_39; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_31);
lean_dec_ref(x_1);
x_39 = l_Lean_Expr_hasMVar(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_30);
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_32 = x_41;
x_33 = x_39;
goto block_38;
}
else
{
lean_object* x_42; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_42 = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_30, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
x_32 = x_42;
x_33 = x_44;
goto block_38;
}
else
{
lean_dec_ref(x_31);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_42;
}
}
block_38:
{
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec_ref(x_32);
x_34 = l_Lean_Expr_hasMVar(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_31);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
x_1 = x_31;
goto _start;
}
}
else
{
lean_dec_ref(x_31);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_32;
}
}
}
case 6:
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_46);
lean_dec_ref(x_1);
x_15 = x_45;
x_16 = x_46;
goto block_23;
}
case 7:
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_48);
lean_dec_ref(x_1);
x_15 = x_47;
x_16 = x_48;
goto block_23;
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_59; uint8_t x_60; uint8_t x_68; 
x_49 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_49);
x_50 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_51);
lean_dec_ref(x_1);
x_68 = l_Lean_Expr_hasMVar(x_49);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_49);
x_69 = lean_box(x_68);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_59 = x_70;
x_60 = x_68;
goto block_67;
}
else
{
lean_object* x_71; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_71 = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_49, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
x_59 = x_71;
x_60 = x_73;
goto block_67;
}
else
{
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_71;
}
}
block_58:
{
if (x_53 == 0)
{
uint8_t x_54; 
lean_dec_ref(x_52);
x_54 = l_Lean_Expr_hasMVar(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_51);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
x_1 = x_51;
goto _start;
}
}
else
{
lean_dec_ref(x_51);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_52;
}
}
block_67:
{
if (x_60 == 0)
{
uint8_t x_61; 
lean_dec_ref(x_59);
x_61 = l_Lean_Expr_hasMVar(x_50);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_50);
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_52 = x_63;
x_53 = x_61;
goto block_58;
}
else
{
lean_object* x_64; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_64 = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_50, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
x_52 = x_64;
x_53 = x_66;
goto block_58;
}
else
{
lean_dec_ref(x_51);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_64;
}
}
}
else
{
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_59;
}
}
}
case 10:
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_74);
lean_dec_ref(x_1);
x_75 = l_Lean_Expr_hasMVar(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_74);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
return x_77;
}
else
{
x_1 = x_74;
goto _start;
}
}
case 11:
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_79);
lean_dec_ref(x_1);
x_80 = l_Lean_Expr_hasMVar(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_79);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_81 = lean_box(x_80);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
else
{
x_1 = x_79;
goto _start;
}
}
default: 
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_84 = 0;
x_85 = lean_box(x_84);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
block_14:
{
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec_ref(x_8);
x_10 = l_Lean_Expr_hasMVar(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
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
block_23:
{
uint8_t x_17; 
x_17 = l_Lean_Expr_hasMVar(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_15);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_7 = x_16;
x_8 = x_19;
x_9 = x_17;
goto block_14;
}
else
{
lean_object* x_20; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_20 = l_Lean_hasAssignableMVar___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(x_15, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
x_7 = x_16;
x_8 = x_20;
x_9 = x_22;
goto block_14;
}
else
{
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_20;
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
lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_174; 
x_17 = lean_ctor_get(x_4, 1);
x_174 = !lean_is_exclusive(x_4);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_4, 0);
lean_dec(x_175);
x_18 = x_4;
x_19 = x_174;
goto block_173;
}
else
{
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = x_174;
goto block_173;
}
block_173:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_17, 2);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_21, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_23);
x_25 = x_18;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_17);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_29; uint8_t x_30; uint8_t x_169; 
lean_inc(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
x_169 = !lean_is_exclusive(x_17);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_17, 2);
lean_dec(x_170);
x_171 = lean_ctor_get(x_17, 1);
lean_dec(x_171);
x_172 = lean_ctor_get(x_17, 0);
lean_dec(x_172);
x_29 = x_17;
x_30 = x_169;
goto block_168;
}
else
{
lean_dec(x_17);
x_29 = lean_box(0);
x_30 = x_169;
goto block_168;
}
block_168:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_array_fget(x_20, x_21);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_21, x_32);
lean_dec(x_21);
if (x_30 == 0)
{
lean_ctor_set(x_29, 1, x_33);
x_34 = x_29;
goto block_166;
}
else
{
lean_object* x_167; 
x_167 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_167, 0, x_20);
lean_ctor_set(x_167, 1, x_33);
lean_ctor_set(x_167, 2, x_22);
x_34 = x_167;
goto block_166;
}
block_166:
{
uint8_t x_35; 
x_35 = lean_unbox(x_31);
lean_dec(x_31);
if (x_35 == 0)
{
lean_object* x_36; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_34);
lean_ctor_set(x_18, 0, x_23);
x_36 = x_18;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_34);
x_36 = x_38;
goto block_37;
}
block_37:
{
x_10 = x_36;
goto block_14;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_106; 
x_39 = lean_array_uget_borrowed(x_1, x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_39);
x_106 = lean_infer_type(x_39, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_108 = l_Lean_Meta_matchEq_x3f(x_107, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
if (lean_obj_tag(x_109) == 1)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_148; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_ctor_get(x_111, 0);
x_148 = !lean_is_exclusive(x_111);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_111, 1);
lean_dec(x_149);
x_113 = x_111;
x_114 = x_148;
goto block_147;
}
else
{
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_box(0);
x_114 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_115; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_115 = l_Lean_Meta_mkEqRefl(x_112, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_39);
x_117 = l_Lean_Meta_isExprDefEq(x_39, x_116, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_130; 
x_118 = lean_ctor_get(x_117, 0);
x_130 = !lean_is_exclusive(x_117);
if (x_130 == 0)
{
x_119 = x_117;
x_120 = x_130;
goto block_129;
}
else
{
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_box(0);
x_120 = x_130;
goto block_129;
}
block_129:
{
uint8_t x_121; 
x_121 = lean_unbox(x_118);
lean_dec(x_118);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_del_object(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_122 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (x_114 == 0)
{
lean_ctor_set(x_113, 1, x_34);
lean_ctor_set(x_113, 0, x_122);
x_123 = x_113;
goto block_127;
}
else
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_122);
lean_ctor_set(x_128, 1, x_34);
x_123 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_124; 
if (x_120 == 0)
{
lean_ctor_set(x_119, 0, x_123);
x_124 = x_119;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_126, 0, x_123);
x_124 = x_126;
goto block_125;
}
block_125:
{
return x_124;
}
}
}
else
{
lean_del_object(x_119);
lean_del_object(x_113);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_40 = x_5;
x_41 = x_6;
x_42 = x_7;
x_43 = x_8;
goto block_105;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_138; 
lean_del_object(x_113);
lean_dec_ref(x_34);
lean_del_object(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_131 = lean_ctor_get(x_117, 0);
x_138 = !lean_is_exclusive(x_117);
if (x_138 == 0)
{
x_132 = x_117;
x_133 = x_138;
goto block_137;
}
else
{
lean_inc(x_131);
lean_dec(x_117);
x_132 = lean_box(0);
x_133 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_134; 
if (x_133 == 0)
{
x_134 = x_132;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_131);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_146; 
lean_del_object(x_113);
lean_dec_ref(x_34);
lean_del_object(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_139 = lean_ctor_get(x_115, 0);
x_146 = !lean_is_exclusive(x_115);
if (x_146 == 0)
{
x_140 = x_115;
x_141 = x_146;
goto block_145;
}
else
{
lean_inc(x_139);
lean_dec(x_115);
x_140 = lean_box(0);
x_141 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_142; 
if (x_141 == 0)
{
x_142 = x_140;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_139);
x_142 = x_144;
goto block_143;
}
block_143:
{
return x_142;
}
}
}
}
}
else
{
lean_dec(x_109);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_40 = x_5;
x_41 = x_6;
x_42 = x_7;
x_43 = x_8;
goto block_105;
}
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_157; 
lean_dec_ref(x_34);
lean_del_object(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_150 = lean_ctor_get(x_108, 0);
x_157 = !lean_is_exclusive(x_108);
if (x_157 == 0)
{
x_151 = x_108;
x_152 = x_157;
goto block_156;
}
else
{
lean_inc(x_150);
lean_dec(x_108);
x_151 = lean_box(0);
x_152 = x_157;
goto block_156;
}
block_156:
{
lean_object* x_153; 
if (x_152 == 0)
{
x_153 = x_151;
goto block_154;
}
else
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_150);
x_153 = x_155;
goto block_154;
}
block_154:
{
return x_153;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_165; 
lean_dec_ref(x_34);
lean_del_object(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_158 = lean_ctor_get(x_106, 0);
x_165 = !lean_is_exclusive(x_106);
if (x_165 == 0)
{
x_159 = x_106;
x_160 = x_165;
goto block_164;
}
else
{
lean_inc(x_158);
lean_dec(x_106);
x_159 = lean_box(0);
x_160 = x_165;
goto block_164;
}
block_164:
{
lean_object* x_161; 
if (x_160 == 0)
{
x_161 = x_159;
goto block_162;
}
else
{
lean_object* x_163; 
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_158);
x_161 = x_163;
goto block_162;
}
block_162:
{
return x_161;
}
}
}
block_105:
{
lean_object* x_44; 
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
x_44 = lean_infer_type(x_39, x_40, x_41, x_42, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc_ref(x_40);
x_46 = l_Lean_Meta_matchHEq_x3f(x_45, x_40, x_41, x_42, x_43);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc_ref(x_40);
x_51 = l_Lean_Meta_mkHEqRefl(x_50, x_40, x_41, x_42, x_43);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
lean_inc(x_39);
x_53 = l_Lean_Meta_isExprDefEq(x_39, x_52, x_40, x_41, x_42, x_43);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_69; 
x_54 = lean_ctor_get(x_53, 0);
x_69 = !lean_is_exclusive(x_53);
if (x_69 == 0)
{
x_55 = x_53;
x_56 = x_69;
goto block_68;
}
else
{
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_box(0);
x_56 = x_69;
goto block_68;
}
block_68:
{
uint8_t x_57; 
x_57 = lean_unbox(x_54);
lean_dec(x_54);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_58 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_34);
lean_ctor_set(x_18, 0, x_58);
x_59 = x_18;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_34);
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
lean_object* x_65; 
lean_del_object(x_55);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_34);
lean_ctor_set(x_18, 0, x_23);
x_65 = x_18;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_23);
lean_ctor_set(x_67, 1, x_34);
x_65 = x_67;
goto block_66;
}
block_66:
{
x_10 = x_65;
goto block_14;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
lean_dec_ref(x_34);
lean_del_object(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_70 = lean_ctor_get(x_53, 0);
x_77 = !lean_is_exclusive(x_53);
if (x_77 == 0)
{
x_71 = x_53;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_53);
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
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_34);
lean_del_object(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_78 = lean_ctor_get(x_51, 0);
x_85 = !lean_is_exclusive(x_51);
if (x_85 == 0)
{
x_79 = x_51;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_51);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_47);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_34);
lean_ctor_set(x_18, 0, x_23);
x_86 = x_18;
goto block_87;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_23);
lean_ctor_set(x_88, 1, x_34);
x_86 = x_88;
goto block_87;
}
block_87:
{
x_10 = x_86;
goto block_14;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_34);
lean_del_object(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_89 = lean_ctor_get(x_46, 0);
x_96 = !lean_is_exclusive(x_46);
if (x_96 == 0)
{
x_90 = x_46;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_46);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_104; 
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_34);
lean_del_object(x_18);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_97 = lean_ctor_get(x_44, 0);
x_104 = !lean_is_exclusive(x_44);
if (x_104 == 0)
{
x_98 = x_44;
x_99 = x_104;
goto block_103;
}
else
{
lean_inc(x_97);
lean_dec(x_44);
x_98 = lean_box(0);
x_99 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_100; 
if (x_99 == 0)
{
x_100 = x_98;
goto block_101;
}
else
{
lean_object* x_102; 
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_97);
x_100 = x_102;
goto block_101;
}
block_101:
{
return x_100;
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
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_682; 
x_14 = lean_ctor_get(x_6, 1);
x_682 = !lean_is_exclusive(x_6);
if (x_682 == 0)
{
lean_object* x_683; 
x_683 = lean_ctor_get(x_6, 0);
lean_dec(x_683);
x_15 = x_6;
x_16 = x_682;
goto block_681;
}
else
{
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_682;
goto block_681;
}
block_681:
{
lean_object* x_17; lean_object* x_24; lean_object* x_25; lean_object* x_31; 
x_24 = lean_box(0);
x_31 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_del_object(x_15);
x_25 = x_14;
goto block_30;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_680; 
x_32 = lean_ctor_get(x_31, 0);
x_680 = !lean_is_exclusive(x_31);
if (x_680 == 0)
{
x_33 = x_31;
x_34 = x_680;
goto block_679;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_680;
goto block_679;
}
block_679:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_126; uint8_t x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_35 = lean_box(0);
x_76 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
x_104 = l_Lean_LocalDecl_isImplementationDetail(x_32);
if (x_104 == 0)
{
lean_object* x_148; uint8_t x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_158; uint8_t x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_168; uint8_t x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_178; uint8_t x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_269; uint8_t x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_277; uint8_t x_278; lean_object* x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_287; uint8_t x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_306; uint8_t x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; uint8_t x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_616; 
x_148 = l_Lean_LocalDecl_type(x_32);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_148);
x_616 = l_Lean_Meta_matchNot_x3f(x_148, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
lean_dec_ref(x_616);
if (lean_obj_tag(x_617) == 1)
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
lean_dec_ref(x_617);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_619 = l_Lean_Meta_findLocalDeclWithType_x3f(x_618, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
lean_dec_ref(x_619);
if (lean_obj_tag(x_620) == 1)
{
lean_object* x_621; lean_object* x_622; uint8_t x_623; uint8_t x_662; 
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec_ref(x_1);
x_621 = lean_ctor_get(x_620, 0);
x_662 = !lean_is_exclusive(x_620);
if (x_662 == 0)
{
x_622 = x_620;
x_623 = x_662;
goto block_661;
}
else
{
lean_inc(x_621);
lean_dec(x_620);
x_622 = lean_box(0);
x_623 = x_662;
goto block_661;
}
block_661:
{
lean_object* x_624; 
lean_inc(x_2);
x_624 = l_Lean_MVarId_getType(x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
lean_dec_ref(x_624);
x_626 = l_Lean_LocalDecl_toExpr(x_32);
x_627 = l_Lean_mkFVar(x_621);
x_628 = l_Lean_Expr_app___override(x_626, x_627);
lean_inc(x_8);
x_629 = l_Lean_Meta_mkFalseElim(x_625, x_628, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
lean_dec_ref(x_629);
x_631 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_630, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; 
lean_dec_ref(x_631);
x_632 = lean_box(x_12);
if (x_623 == 0)
{
lean_ctor_set(x_622, 0, x_632);
x_633 = x_622;
goto block_635;
}
else
{
lean_object* x_636; 
x_636 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_636, 0, x_632);
x_633 = x_636;
goto block_635;
}
block_635:
{
lean_object* x_634; 
x_634 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_35);
x_17 = x_634;
goto block_23;
}
}
else
{
lean_object* x_637; lean_object* x_638; uint8_t x_639; uint8_t x_644; 
lean_del_object(x_622);
lean_del_object(x_15);
lean_dec(x_14);
x_637 = lean_ctor_get(x_631, 0);
x_644 = !lean_is_exclusive(x_631);
if (x_644 == 0)
{
x_638 = x_631;
x_639 = x_644;
goto block_643;
}
else
{
lean_inc(x_637);
lean_dec(x_631);
x_638 = lean_box(0);
x_639 = x_644;
goto block_643;
}
block_643:
{
lean_object* x_640; 
if (x_639 == 0)
{
x_640 = x_638;
goto block_641;
}
else
{
lean_object* x_642; 
x_642 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_642, 0, x_637);
x_640 = x_642;
goto block_641;
}
block_641:
{
return x_640;
}
}
}
}
else
{
lean_object* x_645; lean_object* x_646; uint8_t x_647; uint8_t x_652; 
lean_del_object(x_622);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
x_645 = lean_ctor_get(x_629, 0);
x_652 = !lean_is_exclusive(x_629);
if (x_652 == 0)
{
x_646 = x_629;
x_647 = x_652;
goto block_651;
}
else
{
lean_inc(x_645);
lean_dec(x_629);
x_646 = lean_box(0);
x_647 = x_652;
goto block_651;
}
block_651:
{
lean_object* x_648; 
if (x_647 == 0)
{
x_648 = x_646;
goto block_649;
}
else
{
lean_object* x_650; 
x_650 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_650, 0, x_645);
x_648 = x_650;
goto block_649;
}
block_649:
{
return x_648;
}
}
}
}
else
{
lean_object* x_653; lean_object* x_654; uint8_t x_655; uint8_t x_660; 
lean_del_object(x_622);
lean_dec(x_621);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_653 = lean_ctor_get(x_624, 0);
x_660 = !lean_is_exclusive(x_624);
if (x_660 == 0)
{
x_654 = x_624;
x_655 = x_660;
goto block_659;
}
else
{
lean_inc(x_653);
lean_dec(x_624);
x_654 = lean_box(0);
x_655 = x_660;
goto block_659;
}
block_659:
{
lean_object* x_656; 
if (x_655 == 0)
{
x_656 = x_654;
goto block_657;
}
else
{
lean_object* x_658; 
x_658 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_658, 0, x_653);
x_656 = x_658;
goto block_657;
}
block_657:
{
return x_656;
}
}
}
}
}
else
{
lean_dec(x_620);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_481 = x_7;
x_482 = x_8;
x_483 = x_9;
x_484 = x_10;
goto block_615;
}
}
else
{
lean_object* x_663; lean_object* x_664; uint8_t x_665; uint8_t x_670; 
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_663 = lean_ctor_get(x_619, 0);
x_670 = !lean_is_exclusive(x_619);
if (x_670 == 0)
{
x_664 = x_619;
x_665 = x_670;
goto block_669;
}
else
{
lean_inc(x_663);
lean_dec(x_619);
x_664 = lean_box(0);
x_665 = x_670;
goto block_669;
}
block_669:
{
lean_object* x_666; 
if (x_665 == 0)
{
x_666 = x_664;
goto block_667;
}
else
{
lean_object* x_668; 
x_668 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_668, 0, x_663);
x_666 = x_668;
goto block_667;
}
block_667:
{
return x_666;
}
}
}
}
else
{
lean_dec(x_617);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_481 = x_7;
x_482 = x_8;
x_483 = x_9;
x_484 = x_10;
goto block_615;
}
}
else
{
lean_object* x_671; lean_object* x_672; uint8_t x_673; uint8_t x_678; 
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_671 = lean_ctor_get(x_616, 0);
x_678 = !lean_is_exclusive(x_616);
if (x_678 == 0)
{
x_672 = x_616;
x_673 = x_678;
goto block_677;
}
else
{
lean_inc(x_671);
lean_dec(x_616);
x_672 = lean_box(0);
x_673 = x_678;
goto block_677;
}
block_677:
{
lean_object* x_674; 
if (x_673 == 0)
{
x_674 = x_672;
goto block_675;
}
else
{
lean_object* x_676; 
x_676 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_676, 0, x_671);
x_674 = x_676;
goto block_675;
}
block_675:
{
return x_674;
}
}
}
block_157:
{
uint8_t x_155; 
x_155 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_155 == 0)
{
lean_dec_ref(x_148);
x_126 = x_154;
x_127 = x_149;
x_128 = x_151;
x_129 = x_150;
x_130 = x_152;
x_131 = x_153;
x_132 = x_104;
goto block_147;
}
else
{
uint8_t x_156; 
x_156 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_148);
x_126 = x_154;
x_127 = x_149;
x_128 = x_151;
x_129 = x_150;
x_130 = x_152;
x_131 = x_153;
x_132 = x_156;
goto block_147;
}
}
block_167:
{
if (x_165 == 0)
{
lean_dec_ref(x_163);
x_149 = x_159;
x_150 = x_160;
x_151 = x_164;
x_152 = x_162;
x_153 = x_161;
x_154 = x_158;
goto block_157;
}
else
{
lean_object* x_166; 
lean_dec_ref(x_164);
lean_dec(x_162);
lean_dec_ref(x_161);
lean_dec(x_158);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_163);
return x_166;
}
}
block_177:
{
uint8_t x_175; 
x_175 = l_Lean_Exception_isInterrupt(x_174);
if (x_175 == 0)
{
uint8_t x_176; 
lean_inc_ref(x_174);
x_176 = l_Lean_Exception_isRuntime(x_174);
x_158 = x_168;
x_159 = x_169;
x_160 = x_170;
x_161 = x_172;
x_162 = x_171;
x_163 = x_174;
x_164 = x_173;
x_165 = x_176;
goto block_167;
}
else
{
x_158 = x_168;
x_159 = x_169;
x_160 = x_170;
x_161 = x_172;
x_162 = x_171;
x_163 = x_174;
x_164 = x_173;
x_165 = x_175;
goto block_167;
}
}
block_268:
{
lean_object* x_184; 
lean_inc(x_178);
lean_inc_ref(x_181);
lean_inc(x_182);
lean_inc_ref(x_183);
lean_inc_ref(x_148);
x_184 = l_Lean_Meta_mkDecide(x_148, x_183, x_182, x_181, x_178);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; lean_object* x_205; uint8_t x_206; uint8_t x_266; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = l_Lean_Meta_Context_config(x_183);
x_187 = lean_ctor_get_uint8(x_186, 0);
x_188 = lean_ctor_get_uint8(x_186, 1);
x_189 = lean_ctor_get_uint8(x_186, 2);
x_190 = lean_ctor_get_uint8(x_186, 3);
x_191 = lean_ctor_get_uint8(x_186, 4);
x_192 = lean_ctor_get_uint8(x_186, 5);
x_193 = lean_ctor_get_uint8(x_186, 6);
x_194 = lean_ctor_get_uint8(x_186, 7);
x_195 = lean_ctor_get_uint8(x_186, 8);
x_196 = lean_ctor_get_uint8(x_186, 10);
x_197 = lean_ctor_get_uint8(x_186, 11);
x_198 = lean_ctor_get_uint8(x_186, 12);
x_199 = lean_ctor_get_uint8(x_186, 13);
x_200 = lean_ctor_get_uint8(x_186, 14);
x_201 = lean_ctor_get_uint8(x_186, 15);
x_202 = lean_ctor_get_uint8(x_186, 16);
x_203 = lean_ctor_get_uint8(x_186, 17);
x_204 = lean_ctor_get_uint8(x_186, 18);
x_266 = !lean_is_exclusive(x_186);
if (x_266 == 0)
{
x_205 = x_186;
x_206 = x_266;
goto block_265;
}
else
{
lean_dec(x_186);
x_205 = lean_box(0);
x_206 = x_266;
goto block_265;
}
block_265:
{
uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; lean_object* x_218; 
x_207 = lean_ctor_get_uint8(x_183, sizeof(void*)*7);
x_208 = lean_ctor_get(x_183, 1);
x_209 = lean_ctor_get(x_183, 2);
x_210 = lean_ctor_get(x_183, 3);
x_211 = lean_ctor_get(x_183, 4);
x_212 = lean_ctor_get(x_183, 5);
x_213 = lean_ctor_get(x_183, 6);
x_214 = lean_ctor_get_uint8(x_183, sizeof(void*)*7 + 1);
x_215 = lean_ctor_get_uint8(x_183, sizeof(void*)*7 + 2);
x_216 = lean_ctor_get_uint8(x_183, sizeof(void*)*7 + 3);
x_217 = 1;
if (x_206 == 0)
{
x_218 = x_205;
goto block_263;
}
else
{
lean_object* x_264; 
x_264 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_264, 0, x_187);
lean_ctor_set_uint8(x_264, 1, x_188);
lean_ctor_set_uint8(x_264, 2, x_189);
lean_ctor_set_uint8(x_264, 3, x_190);
lean_ctor_set_uint8(x_264, 4, x_191);
lean_ctor_set_uint8(x_264, 5, x_192);
lean_ctor_set_uint8(x_264, 6, x_193);
lean_ctor_set_uint8(x_264, 7, x_194);
lean_ctor_set_uint8(x_264, 8, x_195);
lean_ctor_set_uint8(x_264, 10, x_196);
lean_ctor_set_uint8(x_264, 11, x_197);
lean_ctor_set_uint8(x_264, 12, x_198);
lean_ctor_set_uint8(x_264, 13, x_199);
lean_ctor_set_uint8(x_264, 14, x_200);
lean_ctor_set_uint8(x_264, 15, x_201);
lean_ctor_set_uint8(x_264, 16, x_202);
lean_ctor_set_uint8(x_264, 17, x_203);
lean_ctor_set_uint8(x_264, 18, x_204);
x_218 = x_264;
goto block_263;
}
block_263:
{
uint64_t x_219; uint64_t x_220; uint64_t x_221; uint64_t x_222; uint64_t x_223; uint64_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_ctor_set_uint8(x_218, 9, x_217);
x_219 = l_Lean_Meta_Context_configKey(x_183);
x_220 = 2;
x_221 = lean_uint64_shift_right(x_219, x_220);
x_222 = lean_uint64_shift_left(x_221, x_220);
x_223 = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
x_224 = lean_uint64_lor(x_222, x_223);
x_225 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_225, 0, x_218);
lean_ctor_set_uint64(x_225, sizeof(void*)*1, x_224);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc_ref(x_210);
lean_inc_ref(x_209);
lean_inc(x_208);
x_226 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_208);
lean_ctor_set(x_226, 2, x_209);
lean_ctor_set(x_226, 3, x_210);
lean_ctor_set(x_226, 4, x_211);
lean_ctor_set(x_226, 5, x_212);
lean_ctor_set(x_226, 6, x_213);
lean_ctor_set_uint8(x_226, sizeof(void*)*7, x_207);
lean_ctor_set_uint8(x_226, sizeof(void*)*7 + 1, x_214);
lean_ctor_set_uint8(x_226, sizeof(void*)*7 + 2, x_215);
lean_ctor_set_uint8(x_226, sizeof(void*)*7 + 3, x_216);
lean_inc(x_178);
lean_inc_ref(x_181);
lean_inc(x_182);
lean_inc(x_185);
x_227 = lean_whnf(x_185, x_226, x_182, x_181, x_178);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec_ref(x_227);
x_229 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
x_230 = l_Lean_Expr_isConstOf(x_228, x_229);
lean_dec(x_228);
if (x_230 == 0)
{
lean_dec(x_185);
x_149 = x_179;
x_150 = x_180;
x_151 = x_183;
x_152 = x_182;
x_153 = x_181;
x_154 = x_178;
goto block_157;
}
else
{
lean_object* x_231; 
lean_inc(x_178);
lean_inc_ref(x_181);
lean_inc(x_182);
lean_inc_ref(x_183);
lean_inc(x_185);
x_231 = l_Lean_Meta_mkEqRefl(x_185, x_183, x_182, x_181, x_178);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec_ref(x_231);
lean_inc(x_2);
x_233 = l_Lean_MVarId_getType(x_2, x_183, x_182, x_181, x_178);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
lean_dec_ref(x_233);
x_235 = l_Lean_Expr_getAppNumArgs(x_185);
x_236 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
x_237 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(x_235);
x_238 = lean_mk_array(x_235, x_237);
x_239 = lean_unsigned_to_nat(1u);
x_240 = lean_nat_sub(x_235, x_239);
lean_dec(x_235);
x_241 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_185, x_238, x_240);
x_242 = lean_array_push(x_241, x_232);
x_243 = l_Lean_mkAppN(x_236, x_242);
lean_dec_ref(x_242);
lean_inc(x_32);
x_244 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_178);
lean_inc_ref(x_181);
lean_inc(x_182);
lean_inc_ref(x_183);
x_245 = l_Lean_Meta_mkAbsurd(x_234, x_244, x_243, x_183, x_182, x_181, x_178);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
lean_inc(x_2);
x_247 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_246, x_182);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; uint8_t x_249; uint8_t x_256; 
lean_dec_ref(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_178);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_256 = !lean_is_exclusive(x_247);
if (x_256 == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_247, 0);
lean_dec(x_257);
x_248 = x_247;
x_249 = x_256;
goto block_255;
}
else
{
lean_dec(x_247);
x_248 = lean_box(0);
x_249 = x_256;
goto block_255;
}
block_255:
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_box(x_12);
if (x_249 == 0)
{
lean_ctor_set_tag(x_248, 1);
lean_ctor_set(x_248, 0, x_250);
x_251 = x_248;
goto block_253;
}
else
{
lean_object* x_254; 
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_250);
x_251 = x_254;
goto block_253;
}
block_253:
{
lean_object* x_252; 
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_35);
x_17 = x_252;
goto block_23;
}
}
}
else
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_247, 0);
lean_inc(x_258);
lean_dec_ref(x_247);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_182;
x_172 = x_181;
x_173 = x_183;
x_174 = x_258;
goto block_177;
}
}
else
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_245, 0);
lean_inc(x_259);
lean_dec_ref(x_245);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_182;
x_172 = x_181;
x_173 = x_183;
x_174 = x_259;
goto block_177;
}
}
else
{
lean_object* x_260; 
lean_dec(x_232);
lean_dec(x_185);
x_260 = lean_ctor_get(x_233, 0);
lean_inc(x_260);
lean_dec_ref(x_233);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_182;
x_172 = x_181;
x_173 = x_183;
x_174 = x_260;
goto block_177;
}
}
else
{
lean_object* x_261; 
lean_dec(x_185);
x_261 = lean_ctor_get(x_231, 0);
lean_inc(x_261);
lean_dec_ref(x_231);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_182;
x_172 = x_181;
x_173 = x_183;
x_174 = x_261;
goto block_177;
}
}
}
else
{
lean_object* x_262; 
lean_dec(x_185);
x_262 = lean_ctor_get(x_227, 0);
lean_inc(x_262);
lean_dec_ref(x_227);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_182;
x_172 = x_181;
x_173 = x_183;
x_174 = x_262;
goto block_177;
}
}
}
}
else
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_184, 0);
lean_inc(x_267);
lean_dec_ref(x_184);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_182;
x_172 = x_181;
x_173 = x_183;
x_174 = x_267;
goto block_177;
}
}
block_276:
{
if (x_275 == 0)
{
x_149 = x_270;
x_150 = x_271;
x_151 = x_274;
x_152 = x_273;
x_153 = x_272;
x_154 = x_269;
goto block_157;
}
else
{
x_178 = x_269;
x_179 = x_270;
x_180 = x_271;
x_181 = x_272;
x_182 = x_273;
x_183 = x_274;
goto block_268;
}
}
block_286:
{
if (x_284 == 0)
{
lean_dec_ref(x_279);
x_269 = x_277;
x_270 = x_278;
x_271 = x_280;
x_272 = x_282;
x_273 = x_281;
x_274 = x_283;
x_275 = x_104;
goto block_276;
}
else
{
uint8_t x_285; 
x_285 = l_Lean_Expr_hasFVar(x_279);
lean_dec_ref(x_279);
if (x_285 == 0)
{
x_178 = x_277;
x_179 = x_278;
x_180 = x_280;
x_181 = x_282;
x_182 = x_281;
x_183 = x_283;
goto block_268;
}
else
{
x_269 = x_277;
x_270 = x_278;
x_271 = x_280;
x_272 = x_282;
x_273 = x_281;
x_274 = x_283;
x_275 = x_104;
goto block_276;
}
}
}
block_305:
{
lean_object* x_294; 
lean_inc_ref(x_148);
x_294 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_148, x_291);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec_ref(x_294);
x_296 = l_Lean_Expr_hasMVar(x_295);
if (x_296 == 0)
{
x_277 = x_287;
x_278 = x_288;
x_279 = x_295;
x_280 = x_289;
x_281 = x_291;
x_282 = x_290;
x_283 = x_292;
x_284 = x_293;
goto block_286;
}
else
{
x_277 = x_287;
x_278 = x_288;
x_279 = x_295;
x_280 = x_289;
x_281 = x_291;
x_282 = x_290;
x_283 = x_292;
x_284 = x_104;
goto block_286;
}
}
else
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; uint8_t x_304; 
lean_dec_ref(x_292);
lean_dec(x_291);
lean_dec_ref(x_290);
lean_dec(x_287);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_297 = lean_ctor_get(x_294, 0);
x_304 = !lean_is_exclusive(x_294);
if (x_304 == 0)
{
x_298 = x_294;
x_299 = x_304;
goto block_303;
}
else
{
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_box(0);
x_299 = x_304;
goto block_303;
}
block_303:
{
lean_object* x_300; 
if (x_299 == 0)
{
x_300 = x_298;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_297);
x_300 = x_302;
goto block_301;
}
block_301:
{
return x_300;
}
}
}
}
block_313:
{
if (x_312 == 0)
{
x_149 = x_307;
x_150 = x_308;
x_151 = x_311;
x_152 = x_310;
x_153 = x_309;
x_154 = x_306;
goto block_157;
}
else
{
x_287 = x_306;
x_288 = x_307;
x_289 = x_308;
x_290 = x_309;
x_291 = x_310;
x_292 = x_311;
x_293 = x_312;
goto block_305;
}
}
block_322:
{
uint8_t x_320; 
x_320 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_320 == 0)
{
x_306 = x_319;
x_307 = x_315;
x_308 = x_314;
x_309 = x_318;
x_310 = x_317;
x_311 = x_316;
x_312 = x_104;
goto block_313;
}
else
{
uint8_t x_321; 
x_321 = l_Lean_Expr_hasFVar(x_148);
if (x_321 == 0)
{
x_287 = x_319;
x_288 = x_315;
x_289 = x_314;
x_290 = x_318;
x_291 = x_317;
x_292 = x_316;
x_293 = x_320;
goto block_305;
}
else
{
x_306 = x_319;
x_307 = x_315;
x_308 = x_314;
x_309 = x_318;
x_310 = x_317;
x_311 = x_316;
x_312 = x_104;
goto block_313;
}
}
}
block_384:
{
lean_object* x_330; 
lean_inc(x_326);
lean_inc_ref(x_327);
lean_inc(x_323);
lean_inc_ref(x_325);
x_330 = l_Lean_Meta_isExprDefEq(x_328, x_329, x_325, x_323, x_327, x_326);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; uint8_t x_332; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
lean_dec_ref(x_330);
x_332 = lean_unbox(x_331);
lean_dec(x_331);
if (x_332 == 0)
{
x_314 = x_324;
x_315 = x_12;
x_316 = x_325;
x_317 = x_323;
x_318 = x_327;
x_319 = x_326;
goto block_322;
}
else
{
lean_object* x_333; 
lean_dec_ref(x_148);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_333 = l_Lean_MVarId_getType(x_2, x_325, x_323, x_327, x_326);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
lean_dec_ref(x_333);
x_335 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_326);
lean_inc_ref(x_327);
lean_inc(x_323);
lean_inc_ref(x_325);
x_336 = l_Lean_Meta_mkEqOfHEq(x_335, x_12, x_325, x_323, x_327, x_326);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
lean_dec_ref(x_336);
lean_inc(x_323);
x_338 = l_Lean_Meta_mkNoConfusion(x_334, x_337, x_325, x_323, x_327, x_326);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_339, x_323);
lean_dec(x_323);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec_ref(x_340);
x_341 = lean_box(x_12);
x_342 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_342, 0, x_341);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_35);
x_17 = x_343;
goto block_23;
}
else
{
lean_object* x_344; lean_object* x_345; uint8_t x_346; uint8_t x_351; 
lean_del_object(x_15);
lean_dec(x_14);
x_344 = lean_ctor_get(x_340, 0);
x_351 = !lean_is_exclusive(x_340);
if (x_351 == 0)
{
x_345 = x_340;
x_346 = x_351;
goto block_350;
}
else
{
lean_inc(x_344);
lean_dec(x_340);
x_345 = lean_box(0);
x_346 = x_351;
goto block_350;
}
block_350:
{
lean_object* x_347; 
if (x_346 == 0)
{
x_347 = x_345;
goto block_348;
}
else
{
lean_object* x_349; 
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_344);
x_347 = x_349;
goto block_348;
}
block_348:
{
return x_347;
}
}
}
}
else
{
lean_object* x_352; lean_object* x_353; uint8_t x_354; uint8_t x_359; 
lean_dec(x_323);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_352 = lean_ctor_get(x_338, 0);
x_359 = !lean_is_exclusive(x_338);
if (x_359 == 0)
{
x_353 = x_338;
x_354 = x_359;
goto block_358;
}
else
{
lean_inc(x_352);
lean_dec(x_338);
x_353 = lean_box(0);
x_354 = x_359;
goto block_358;
}
block_358:
{
lean_object* x_355; 
if (x_354 == 0)
{
x_355 = x_353;
goto block_356;
}
else
{
lean_object* x_357; 
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_352);
x_355 = x_357;
goto block_356;
}
block_356:
{
return x_355;
}
}
}
}
else
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_367; 
lean_dec(x_334);
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_323);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_360 = lean_ctor_get(x_336, 0);
x_367 = !lean_is_exclusive(x_336);
if (x_367 == 0)
{
x_361 = x_336;
x_362 = x_367;
goto block_366;
}
else
{
lean_inc(x_360);
lean_dec(x_336);
x_361 = lean_box(0);
x_362 = x_367;
goto block_366;
}
block_366:
{
lean_object* x_363; 
if (x_362 == 0)
{
x_363 = x_361;
goto block_364;
}
else
{
lean_object* x_365; 
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_360);
x_363 = x_365;
goto block_364;
}
block_364:
{
return x_363;
}
}
}
}
else
{
lean_object* x_368; lean_object* x_369; uint8_t x_370; uint8_t x_375; 
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_323);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_368 = lean_ctor_get(x_333, 0);
x_375 = !lean_is_exclusive(x_333);
if (x_375 == 0)
{
x_369 = x_333;
x_370 = x_375;
goto block_374;
}
else
{
lean_inc(x_368);
lean_dec(x_333);
x_369 = lean_box(0);
x_370 = x_375;
goto block_374;
}
block_374:
{
lean_object* x_371; 
if (x_370 == 0)
{
x_371 = x_369;
goto block_372;
}
else
{
lean_object* x_373; 
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_368);
x_371 = x_373;
goto block_372;
}
block_372:
{
return x_371;
}
}
}
}
}
else
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; uint8_t x_383; 
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_323);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_376 = lean_ctor_get(x_330, 0);
x_383 = !lean_is_exclusive(x_330);
if (x_383 == 0)
{
x_377 = x_330;
x_378 = x_383;
goto block_382;
}
else
{
lean_inc(x_376);
lean_dec(x_330);
x_377 = lean_box(0);
x_378 = x_383;
goto block_382;
}
block_382:
{
lean_object* x_379; 
if (x_378 == 0)
{
x_379 = x_377;
goto block_380;
}
else
{
lean_object* x_381; 
x_381 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_381, 0, x_376);
x_379 = x_381;
goto block_380;
}
block_380:
{
return x_379;
}
}
}
}
block_434:
{
lean_object* x_390; 
lean_inc(x_389);
lean_inc_ref(x_388);
lean_inc(x_387);
lean_inc_ref(x_386);
lean_inc_ref(x_148);
x_390 = l_Lean_Meta_matchHEq_x3f(x_148, x_386, x_387, x_388, x_389);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec_ref(x_390);
if (lean_obj_tag(x_391) == 1)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
lean_dec_ref(x_391);
x_393 = lean_ctor_get(x_392, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_392, 0);
lean_inc(x_395);
lean_dec(x_392);
x_396 = lean_ctor_get(x_393, 0);
lean_inc(x_396);
lean_dec(x_393);
x_397 = lean_ctor_get(x_394, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_394, 1);
lean_inc(x_398);
lean_dec(x_394);
lean_inc(x_389);
lean_inc_ref(x_388);
lean_inc(x_387);
lean_inc_ref(x_386);
x_399 = l_Lean_Meta_matchConstructorApp_x3f(x_396, x_386, x_387, x_388, x_389);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
lean_dec_ref(x_399);
if (lean_obj_tag(x_400) == 1)
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
lean_inc(x_389);
lean_inc_ref(x_388);
lean_inc(x_387);
lean_inc_ref(x_386);
x_402 = l_Lean_Meta_matchConstructorApp_x3f(x_398, x_386, x_387, x_388, x_389);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
lean_dec_ref(x_402);
if (lean_obj_tag(x_403) == 1)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_404 = lean_ctor_get(x_401, 0);
lean_inc_ref(x_404);
lean_dec(x_401);
x_405 = lean_ctor_get(x_403, 0);
lean_inc(x_405);
lean_dec_ref(x_403);
x_406 = lean_ctor_get(x_405, 0);
lean_inc_ref(x_406);
lean_dec(x_405);
x_407 = lean_ctor_get(x_404, 0);
lean_inc(x_407);
lean_dec_ref(x_404);
x_408 = lean_ctor_get(x_406, 0);
lean_inc(x_408);
lean_dec_ref(x_406);
x_409 = lean_name_eq(x_407, x_408);
lean_dec(x_408);
lean_dec(x_407);
if (x_409 == 0)
{
x_323 = x_387;
x_324 = x_385;
x_325 = x_386;
x_326 = x_389;
x_327 = x_388;
x_328 = x_395;
x_329 = x_397;
goto block_384;
}
else
{
if (x_104 == 0)
{
lean_dec(x_397);
lean_dec(x_395);
x_314 = x_385;
x_315 = x_12;
x_316 = x_386;
x_317 = x_387;
x_318 = x_388;
x_319 = x_389;
goto block_322;
}
else
{
x_323 = x_387;
x_324 = x_385;
x_325 = x_386;
x_326 = x_389;
x_327 = x_388;
x_328 = x_395;
x_329 = x_397;
goto block_384;
}
}
}
else
{
lean_dec(x_403);
lean_dec(x_401);
lean_dec(x_397);
lean_dec(x_395);
x_314 = x_385;
x_315 = x_12;
x_316 = x_386;
x_317 = x_387;
x_318 = x_388;
x_319 = x_389;
goto block_322;
}
}
else
{
lean_object* x_410; lean_object* x_411; uint8_t x_412; uint8_t x_417; 
lean_dec(x_401);
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_389);
lean_dec_ref(x_388);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_410 = lean_ctor_get(x_402, 0);
x_417 = !lean_is_exclusive(x_402);
if (x_417 == 0)
{
x_411 = x_402;
x_412 = x_417;
goto block_416;
}
else
{
lean_inc(x_410);
lean_dec(x_402);
x_411 = lean_box(0);
x_412 = x_417;
goto block_416;
}
block_416:
{
lean_object* x_413; 
if (x_412 == 0)
{
x_413 = x_411;
goto block_414;
}
else
{
lean_object* x_415; 
x_415 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_415, 0, x_410);
x_413 = x_415;
goto block_414;
}
block_414:
{
return x_413;
}
}
}
}
else
{
lean_dec(x_400);
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_395);
x_314 = x_385;
x_315 = x_12;
x_316 = x_386;
x_317 = x_387;
x_318 = x_388;
x_319 = x_389;
goto block_322;
}
}
else
{
lean_object* x_418; lean_object* x_419; uint8_t x_420; uint8_t x_425; 
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_389);
lean_dec_ref(x_388);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_418 = lean_ctor_get(x_399, 0);
x_425 = !lean_is_exclusive(x_399);
if (x_425 == 0)
{
x_419 = x_399;
x_420 = x_425;
goto block_424;
}
else
{
lean_inc(x_418);
lean_dec(x_399);
x_419 = lean_box(0);
x_420 = x_425;
goto block_424;
}
block_424:
{
lean_object* x_421; 
if (x_420 == 0)
{
x_421 = x_419;
goto block_422;
}
else
{
lean_object* x_423; 
x_423 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_423, 0, x_418);
x_421 = x_423;
goto block_422;
}
block_422:
{
return x_421;
}
}
}
}
else
{
lean_dec(x_391);
x_314 = x_385;
x_315 = x_104;
x_316 = x_386;
x_317 = x_387;
x_318 = x_388;
x_319 = x_389;
goto block_322;
}
}
else
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; uint8_t x_433; 
lean_dec(x_389);
lean_dec_ref(x_388);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_426 = lean_ctor_get(x_390, 0);
x_433 = !lean_is_exclusive(x_390);
if (x_433 == 0)
{
x_427 = x_390;
x_428 = x_433;
goto block_432;
}
else
{
lean_inc(x_426);
lean_dec(x_390);
x_427 = lean_box(0);
x_428 = x_433;
goto block_432;
}
block_432:
{
lean_object* x_429; 
if (x_428 == 0)
{
x_429 = x_427;
goto block_430;
}
else
{
lean_object* x_431; 
x_431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_431, 0, x_426);
x_429 = x_431;
goto block_430;
}
block_430:
{
return x_429;
}
}
}
}
block_480:
{
lean_object* x_439; 
lean_inc(x_438);
lean_inc_ref(x_437);
lean_inc(x_436);
lean_inc_ref(x_435);
lean_inc_ref(x_148);
x_439 = l_Lean_Meta_matchEq_x3f(x_148, x_435, x_436, x_437, x_438);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
lean_dec_ref(x_439);
if (lean_obj_tag(x_440) == 1)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
lean_dec_ref(x_440);
x_442 = lean_ctor_get(x_441, 1);
lean_inc(x_442);
lean_dec(x_441);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
lean_inc(x_438);
lean_inc_ref(x_437);
lean_inc(x_436);
lean_inc_ref(x_435);
x_445 = l_Lean_Meta_matchConstructorApp_x3f(x_443, x_435, x_436, x_437, x_438);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
lean_dec_ref(x_445);
if (lean_obj_tag(x_446) == 1)
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
lean_dec_ref(x_446);
lean_inc(x_438);
lean_inc_ref(x_437);
lean_inc(x_436);
lean_inc_ref(x_435);
x_448 = l_Lean_Meta_matchConstructorApp_x3f(x_444, x_435, x_436, x_437, x_438);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
lean_dec_ref(x_448);
if (lean_obj_tag(x_449) == 1)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; 
x_450 = lean_ctor_get(x_447, 0);
lean_inc_ref(x_450);
lean_dec(x_447);
x_451 = lean_ctor_get(x_449, 0);
lean_inc(x_451);
lean_dec_ref(x_449);
x_452 = lean_ctor_get(x_451, 0);
lean_inc_ref(x_452);
lean_dec(x_451);
x_453 = lean_ctor_get(x_450, 0);
lean_inc(x_453);
lean_dec_ref(x_450);
x_454 = lean_ctor_get(x_452, 0);
lean_inc(x_454);
lean_dec_ref(x_452);
x_455 = lean_name_eq(x_453, x_454);
lean_dec(x_454);
lean_dec(x_453);
if (x_455 == 0)
{
lean_dec_ref(x_148);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_36 = x_438;
x_37 = x_436;
x_38 = x_437;
x_39 = x_435;
goto block_75;
}
else
{
if (x_104 == 0)
{
lean_del_object(x_33);
x_385 = x_12;
x_386 = x_435;
x_387 = x_436;
x_388 = x_437;
x_389 = x_438;
goto block_434;
}
else
{
lean_dec_ref(x_148);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_36 = x_438;
x_37 = x_436;
x_38 = x_437;
x_39 = x_435;
goto block_75;
}
}
}
else
{
lean_dec(x_449);
lean_dec(x_447);
lean_del_object(x_33);
x_385 = x_12;
x_386 = x_435;
x_387 = x_436;
x_388 = x_437;
x_389 = x_438;
goto block_434;
}
}
else
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; uint8_t x_463; 
lean_dec(x_447);
lean_dec(x_438);
lean_dec_ref(x_437);
lean_dec(x_436);
lean_dec_ref(x_435);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_456 = lean_ctor_get(x_448, 0);
x_463 = !lean_is_exclusive(x_448);
if (x_463 == 0)
{
x_457 = x_448;
x_458 = x_463;
goto block_462;
}
else
{
lean_inc(x_456);
lean_dec(x_448);
x_457 = lean_box(0);
x_458 = x_463;
goto block_462;
}
block_462:
{
lean_object* x_459; 
if (x_458 == 0)
{
x_459 = x_457;
goto block_460;
}
else
{
lean_object* x_461; 
x_461 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_461, 0, x_456);
x_459 = x_461;
goto block_460;
}
block_460:
{
return x_459;
}
}
}
}
else
{
lean_dec(x_446);
lean_dec(x_444);
lean_del_object(x_33);
x_385 = x_12;
x_386 = x_435;
x_387 = x_436;
x_388 = x_437;
x_389 = x_438;
goto block_434;
}
}
else
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; uint8_t x_471; 
lean_dec(x_444);
lean_dec(x_438);
lean_dec_ref(x_437);
lean_dec(x_436);
lean_dec_ref(x_435);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_464 = lean_ctor_get(x_445, 0);
x_471 = !lean_is_exclusive(x_445);
if (x_471 == 0)
{
x_465 = x_445;
x_466 = x_471;
goto block_470;
}
else
{
lean_inc(x_464);
lean_dec(x_445);
x_465 = lean_box(0);
x_466 = x_471;
goto block_470;
}
block_470:
{
lean_object* x_467; 
if (x_466 == 0)
{
x_467 = x_465;
goto block_468;
}
else
{
lean_object* x_469; 
x_469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_469, 0, x_464);
x_467 = x_469;
goto block_468;
}
block_468:
{
return x_467;
}
}
}
}
else
{
lean_dec(x_440);
lean_del_object(x_33);
x_385 = x_104;
x_386 = x_435;
x_387 = x_436;
x_388 = x_437;
x_389 = x_438;
goto block_434;
}
}
else
{
lean_object* x_472; lean_object* x_473; uint8_t x_474; uint8_t x_479; 
lean_dec(x_438);
lean_dec_ref(x_437);
lean_dec(x_436);
lean_dec_ref(x_435);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_472 = lean_ctor_get(x_439, 0);
x_479 = !lean_is_exclusive(x_439);
if (x_479 == 0)
{
x_473 = x_439;
x_474 = x_479;
goto block_478;
}
else
{
lean_inc(x_472);
lean_dec(x_439);
x_473 = lean_box(0);
x_474 = x_479;
goto block_478;
}
block_478:
{
lean_object* x_475; 
if (x_474 == 0)
{
x_475 = x_473;
goto block_476;
}
else
{
lean_object* x_477; 
x_477 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_477, 0, x_472);
x_475 = x_477;
goto block_476;
}
block_476:
{
return x_475;
}
}
}
}
block_615:
{
lean_object* x_485; 
lean_inc(x_484);
lean_inc_ref(x_483);
lean_inc(x_482);
lean_inc_ref(x_481);
lean_inc_ref(x_148);
x_485 = l_refutableHasNotBit_x3f(x_148, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
lean_dec_ref(x_485);
if (lean_obj_tag(x_486) == 1)
{
lean_object* x_487; lean_object* x_488; uint8_t x_489; uint8_t x_526; 
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_487 = lean_ctor_get(x_486, 0);
x_526 = !lean_is_exclusive(x_486);
if (x_526 == 0)
{
x_488 = x_486;
x_489 = x_526;
goto block_525;
}
else
{
lean_inc(x_487);
lean_dec(x_486);
x_488 = lean_box(0);
x_489 = x_526;
goto block_525;
}
block_525:
{
lean_object* x_490; 
lean_inc(x_2);
x_490 = l_Lean_MVarId_getType(x_2, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
lean_dec_ref(x_490);
x_492 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_482);
x_493 = l_Lean_Meta_mkAbsurd(x_491, x_487, x_492, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
lean_dec_ref(x_493);
x_495 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_494, x_482);
lean_dec(x_482);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; 
lean_dec_ref(x_495);
x_496 = lean_box(x_12);
if (x_489 == 0)
{
lean_ctor_set(x_488, 0, x_496);
x_497 = x_488;
goto block_499;
}
else
{
lean_object* x_500; 
x_500 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_500, 0, x_496);
x_497 = x_500;
goto block_499;
}
block_499:
{
lean_object* x_498; 
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_35);
x_17 = x_498;
goto block_23;
}
}
else
{
lean_object* x_501; lean_object* x_502; uint8_t x_503; uint8_t x_508; 
lean_del_object(x_488);
lean_del_object(x_15);
lean_dec(x_14);
x_501 = lean_ctor_get(x_495, 0);
x_508 = !lean_is_exclusive(x_495);
if (x_508 == 0)
{
x_502 = x_495;
x_503 = x_508;
goto block_507;
}
else
{
lean_inc(x_501);
lean_dec(x_495);
x_502 = lean_box(0);
x_503 = x_508;
goto block_507;
}
block_507:
{
lean_object* x_504; 
if (x_503 == 0)
{
x_504 = x_502;
goto block_505;
}
else
{
lean_object* x_506; 
x_506 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_506, 0, x_501);
x_504 = x_506;
goto block_505;
}
block_505:
{
return x_504;
}
}
}
}
else
{
lean_object* x_509; lean_object* x_510; uint8_t x_511; uint8_t x_516; 
lean_del_object(x_488);
lean_dec(x_482);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_509 = lean_ctor_get(x_493, 0);
x_516 = !lean_is_exclusive(x_493);
if (x_516 == 0)
{
x_510 = x_493;
x_511 = x_516;
goto block_515;
}
else
{
lean_inc(x_509);
lean_dec(x_493);
x_510 = lean_box(0);
x_511 = x_516;
goto block_515;
}
block_515:
{
lean_object* x_512; 
if (x_511 == 0)
{
x_512 = x_510;
goto block_513;
}
else
{
lean_object* x_514; 
x_514 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_514, 0, x_509);
x_512 = x_514;
goto block_513;
}
block_513:
{
return x_512;
}
}
}
}
else
{
lean_object* x_517; lean_object* x_518; uint8_t x_519; uint8_t x_524; 
lean_del_object(x_488);
lean_dec(x_487);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_517 = lean_ctor_get(x_490, 0);
x_524 = !lean_is_exclusive(x_490);
if (x_524 == 0)
{
x_518 = x_490;
x_519 = x_524;
goto block_523;
}
else
{
lean_inc(x_517);
lean_dec(x_490);
x_518 = lean_box(0);
x_519 = x_524;
goto block_523;
}
block_523:
{
lean_object* x_520; 
if (x_519 == 0)
{
x_520 = x_518;
goto block_521;
}
else
{
lean_object* x_522; 
x_522 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_522, 0, x_517);
x_520 = x_522;
goto block_521;
}
block_521:
{
return x_520;
}
}
}
}
}
else
{
lean_object* x_527; 
lean_dec(x_486);
lean_inc(x_484);
lean_inc_ref(x_483);
lean_inc(x_482);
lean_inc_ref(x_481);
lean_inc_ref(x_148);
x_527 = l_Lean_Meta_matchNe_x3f(x_148, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
lean_dec_ref(x_527);
if (lean_obj_tag(x_528) == 1)
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; uint8_t x_598; 
x_529 = lean_ctor_get(x_528, 0);
x_598 = !lean_is_exclusive(x_528);
if (x_598 == 0)
{
x_530 = x_528;
x_531 = x_598;
goto block_597;
}
else
{
lean_inc(x_529);
lean_dec(x_528);
x_530 = lean_box(0);
x_531 = x_598;
goto block_597;
}
block_597:
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; uint8_t x_596; 
x_532 = lean_ctor_get(x_529, 1);
lean_inc(x_532);
lean_dec(x_529);
x_533 = lean_ctor_get(x_532, 0);
x_534 = lean_ctor_get(x_532, 1);
x_596 = !lean_is_exclusive(x_532);
if (x_596 == 0)
{
x_535 = x_532;
x_536 = x_596;
goto block_595;
}
else
{
lean_inc(x_534);
lean_inc(x_533);
lean_dec(x_532);
x_535 = lean_box(0);
x_536 = x_596;
goto block_595;
}
block_595:
{
lean_object* x_537; 
lean_inc(x_484);
lean_inc_ref(x_483);
lean_inc(x_482);
lean_inc_ref(x_481);
lean_inc(x_533);
x_537 = l_Lean_Meta_isExprDefEq(x_533, x_534, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; uint8_t x_539; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
lean_dec_ref(x_537);
x_539 = lean_unbox(x_538);
lean_dec(x_538);
if (x_539 == 0)
{
lean_del_object(x_535);
lean_dec(x_533);
lean_del_object(x_530);
x_435 = x_481;
x_436 = x_482;
x_437 = x_483;
x_438 = x_484;
goto block_480;
}
else
{
lean_object* x_540; 
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_540 = l_Lean_MVarId_getType(x_2, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; 
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
lean_dec_ref(x_540);
lean_inc(x_484);
lean_inc_ref(x_483);
lean_inc(x_482);
lean_inc_ref(x_481);
x_542 = l_Lean_Meta_mkEqRefl(x_533, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
lean_dec_ref(x_542);
x_544 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_482);
x_545 = l_Lean_Meta_mkAbsurd(x_541, x_543, x_544, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
lean_dec_ref(x_545);
x_547 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_546, x_482);
lean_dec(x_482);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; 
lean_dec_ref(x_547);
x_548 = lean_box(x_12);
if (x_531 == 0)
{
lean_ctor_set(x_530, 0, x_548);
x_549 = x_530;
goto block_553;
}
else
{
lean_object* x_554; 
x_554 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_554, 0, x_548);
x_549 = x_554;
goto block_553;
}
block_553:
{
lean_object* x_550; 
if (x_536 == 0)
{
lean_ctor_set(x_535, 1, x_35);
lean_ctor_set(x_535, 0, x_549);
x_550 = x_535;
goto block_551;
}
else
{
lean_object* x_552; 
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_549);
lean_ctor_set(x_552, 1, x_35);
x_550 = x_552;
goto block_551;
}
block_551:
{
x_17 = x_550;
goto block_23;
}
}
}
else
{
lean_object* x_555; lean_object* x_556; uint8_t x_557; uint8_t x_562; 
lean_del_object(x_535);
lean_del_object(x_530);
lean_del_object(x_15);
lean_dec(x_14);
x_555 = lean_ctor_get(x_547, 0);
x_562 = !lean_is_exclusive(x_547);
if (x_562 == 0)
{
x_556 = x_547;
x_557 = x_562;
goto block_561;
}
else
{
lean_inc(x_555);
lean_dec(x_547);
x_556 = lean_box(0);
x_557 = x_562;
goto block_561;
}
block_561:
{
lean_object* x_558; 
if (x_557 == 0)
{
x_558 = x_556;
goto block_559;
}
else
{
lean_object* x_560; 
x_560 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_560, 0, x_555);
x_558 = x_560;
goto block_559;
}
block_559:
{
return x_558;
}
}
}
}
else
{
lean_object* x_563; lean_object* x_564; uint8_t x_565; uint8_t x_570; 
lean_del_object(x_535);
lean_del_object(x_530);
lean_dec(x_482);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_563 = lean_ctor_get(x_545, 0);
x_570 = !lean_is_exclusive(x_545);
if (x_570 == 0)
{
x_564 = x_545;
x_565 = x_570;
goto block_569;
}
else
{
lean_inc(x_563);
lean_dec(x_545);
x_564 = lean_box(0);
x_565 = x_570;
goto block_569;
}
block_569:
{
lean_object* x_566; 
if (x_565 == 0)
{
x_566 = x_564;
goto block_567;
}
else
{
lean_object* x_568; 
x_568 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_568, 0, x_563);
x_566 = x_568;
goto block_567;
}
block_567:
{
return x_566;
}
}
}
}
else
{
lean_object* x_571; lean_object* x_572; uint8_t x_573; uint8_t x_578; 
lean_dec(x_541);
lean_del_object(x_535);
lean_del_object(x_530);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_571 = lean_ctor_get(x_542, 0);
x_578 = !lean_is_exclusive(x_542);
if (x_578 == 0)
{
x_572 = x_542;
x_573 = x_578;
goto block_577;
}
else
{
lean_inc(x_571);
lean_dec(x_542);
x_572 = lean_box(0);
x_573 = x_578;
goto block_577;
}
block_577:
{
lean_object* x_574; 
if (x_573 == 0)
{
x_574 = x_572;
goto block_575;
}
else
{
lean_object* x_576; 
x_576 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_576, 0, x_571);
x_574 = x_576;
goto block_575;
}
block_575:
{
return x_574;
}
}
}
}
else
{
lean_object* x_579; lean_object* x_580; uint8_t x_581; uint8_t x_586; 
lean_del_object(x_535);
lean_dec(x_533);
lean_del_object(x_530);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_579 = lean_ctor_get(x_540, 0);
x_586 = !lean_is_exclusive(x_540);
if (x_586 == 0)
{
x_580 = x_540;
x_581 = x_586;
goto block_585;
}
else
{
lean_inc(x_579);
lean_dec(x_540);
x_580 = lean_box(0);
x_581 = x_586;
goto block_585;
}
block_585:
{
lean_object* x_582; 
if (x_581 == 0)
{
x_582 = x_580;
goto block_583;
}
else
{
lean_object* x_584; 
x_584 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_584, 0, x_579);
x_582 = x_584;
goto block_583;
}
block_583:
{
return x_582;
}
}
}
}
}
else
{
lean_object* x_587; lean_object* x_588; uint8_t x_589; uint8_t x_594; 
lean_del_object(x_535);
lean_dec(x_533);
lean_del_object(x_530);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_587 = lean_ctor_get(x_537, 0);
x_594 = !lean_is_exclusive(x_537);
if (x_594 == 0)
{
x_588 = x_537;
x_589 = x_594;
goto block_593;
}
else
{
lean_inc(x_587);
lean_dec(x_537);
x_588 = lean_box(0);
x_589 = x_594;
goto block_593;
}
block_593:
{
lean_object* x_590; 
if (x_589 == 0)
{
x_590 = x_588;
goto block_591;
}
else
{
lean_object* x_592; 
x_592 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_592, 0, x_587);
x_590 = x_592;
goto block_591;
}
block_591:
{
return x_590;
}
}
}
}
}
}
else
{
lean_dec(x_528);
x_435 = x_481;
x_436 = x_482;
x_437 = x_483;
x_438 = x_484;
goto block_480;
}
}
else
{
lean_object* x_599; lean_object* x_600; uint8_t x_601; uint8_t x_606; 
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_599 = lean_ctor_get(x_527, 0);
x_606 = !lean_is_exclusive(x_527);
if (x_606 == 0)
{
x_600 = x_527;
x_601 = x_606;
goto block_605;
}
else
{
lean_inc(x_599);
lean_dec(x_527);
x_600 = lean_box(0);
x_601 = x_606;
goto block_605;
}
block_605:
{
lean_object* x_602; 
if (x_601 == 0)
{
x_602 = x_600;
goto block_603;
}
else
{
lean_object* x_604; 
x_604 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_604, 0, x_599);
x_602 = x_604;
goto block_603;
}
block_603:
{
return x_602;
}
}
}
}
}
else
{
lean_object* x_607; lean_object* x_608; uint8_t x_609; uint8_t x_614; 
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_607 = lean_ctor_get(x_485, 0);
x_614 = !lean_is_exclusive(x_485);
if (x_614 == 0)
{
x_608 = x_485;
x_609 = x_614;
goto block_613;
}
else
{
lean_inc(x_607);
lean_dec(x_485);
x_608 = lean_box(0);
x_609 = x_614;
goto block_613;
}
block_613:
{
lean_object* x_610; 
if (x_609 == 0)
{
x_610 = x_608;
goto block_611;
}
else
{
lean_object* x_612; 
x_612 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_612, 0, x_607);
x_610 = x_612;
goto block_611;
}
block_611:
{
return x_610;
}
}
}
}
}
else
{
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_76;
goto block_30;
}
block_75:
{
lean_object* x_40; 
lean_inc(x_2);
x_40 = l_Lean_MVarId_getType(x_2, x_39, x_37, x_38, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_37);
x_43 = l_Lean_Meta_mkNoConfusion(x_41, x_42, x_39, x_37, x_38, x_36);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_44, x_37);
lean_dec(x_37);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_45);
x_46 = lean_box(x_12);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_46);
x_47 = x_33;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_46);
x_47 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
x_17 = x_48;
goto block_23;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_del_object(x_33);
lean_del_object(x_15);
lean_dec(x_14);
x_51 = lean_ctor_get(x_45, 0);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
x_52 = x_45;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_45);
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
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec(x_37);
lean_del_object(x_33);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_59 = lean_ctor_get(x_43, 0);
x_66 = !lean_is_exclusive(x_43);
if (x_66 == 0)
{
x_60 = x_43;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_43);
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
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_67 = lean_ctor_get(x_40, 0);
x_74 = !lean_is_exclusive(x_40);
if (x_74 == 0)
{
x_68 = x_40;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_40);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
block_97:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_1, 0);
x_82 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
lean_inc(x_81);
lean_inc(x_2);
x_83 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_2, x_82, x_81, x_78, x_79, x_80, x_77);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_76;
goto block_30;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_86 = lean_box(x_12);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_35);
x_17 = x_88;
goto block_23;
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_83, 0);
x_96 = !lean_is_exclusive(x_83);
if (x_96 == 0)
{
x_90 = x_83;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
}
block_103:
{
if (x_102 == 0)
{
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec_ref(x_99);
lean_dec(x_98);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_76;
goto block_30;
}
else
{
x_77 = x_98;
x_78 = x_99;
x_79 = x_100;
x_80 = x_101;
goto block_97;
}
}
block_110:
{
if (x_106 == 0)
{
x_77 = x_105;
x_78 = x_107;
x_79 = x_108;
x_80 = x_109;
goto block_97;
}
else
{
x_98 = x_105;
x_99 = x_107;
x_100 = x_108;
x_101 = x_109;
x_102 = x_104;
goto block_103;
}
}
block_117:
{
if (x_116 == 0)
{
x_98 = x_111;
x_99 = x_113;
x_100 = x_114;
x_101 = x_115;
x_102 = x_104;
goto block_103;
}
else
{
x_105 = x_111;
x_106 = x_112;
x_107 = x_113;
x_108 = x_114;
x_109 = x_115;
goto block_110;
}
}
block_125:
{
uint8_t x_124; 
x_124 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_124 == 0)
{
x_111 = x_123;
x_112 = x_118;
x_113 = x_120;
x_114 = x_121;
x_115 = x_122;
x_116 = x_104;
goto block_117;
}
else
{
if (x_119 == 0)
{
x_105 = x_123;
x_106 = x_118;
x_107 = x_120;
x_108 = x_121;
x_109 = x_122;
goto block_110;
}
else
{
x_111 = x_123;
x_112 = x_118;
x_113 = x_120;
x_114 = x_121;
x_115 = x_122;
x_116 = x_104;
goto block_117;
}
}
}
block_147:
{
if (x_132 == 0)
{
x_118 = x_127;
x_119 = x_129;
x_120 = x_128;
x_121 = x_130;
x_122 = x_131;
x_123 = x_126;
goto block_125;
}
else
{
lean_object* x_133; 
lean_inc(x_126);
lean_inc_ref(x_131);
lean_inc(x_130);
lean_inc_ref(x_128);
lean_inc(x_32);
lean_inc(x_2);
x_133 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_2, x_32, x_128, x_130, x_131, x_126);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
x_118 = x_127;
x_119 = x_129;
x_120 = x_128;
x_121 = x_130;
x_122 = x_131;
x_123 = x_126;
goto block_125;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_128);
lean_dec(x_126);
lean_dec(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_136 = lean_box(x_12);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_35);
x_17 = x_138;
goto block_23;
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_146; 
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec_ref(x_128);
lean_dec(x_126);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_139 = lean_ctor_get(x_133, 0);
x_146 = !lean_is_exclusive(x_133);
if (x_146 == 0)
{
x_140 = x_133;
x_141 = x_146;
goto block_145;
}
else
{
lean_inc(x_139);
lean_dec(x_133);
x_140 = lean_box(0);
x_141 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_142; 
if (x_141 == 0)
{
x_142 = x_140;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_139);
x_142 = x_144;
goto block_143;
}
block_143:
{
return x_142;
}
}
}
}
}
}
}
block_23:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_14);
x_19 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
block_30:
{
lean_object* x_26; size_t x_27; size_t x_28; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_5, x_27);
x_5 = x_28;
x_6 = x_26;
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_682; 
x_14 = lean_ctor_get(x_6, 1);
x_682 = !lean_is_exclusive(x_6);
if (x_682 == 0)
{
lean_object* x_683; 
x_683 = lean_ctor_get(x_6, 0);
lean_dec(x_683);
x_15 = x_6;
x_16 = x_682;
goto block_681;
}
else
{
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_682;
goto block_681;
}
block_681:
{
lean_object* x_17; lean_object* x_24; lean_object* x_25; lean_object* x_31; 
x_24 = lean_box(0);
x_31 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_del_object(x_15);
x_25 = x_14;
goto block_30;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_680; 
x_32 = lean_ctor_get(x_31, 0);
x_680 = !lean_is_exclusive(x_31);
if (x_680 == 0)
{
x_33 = x_31;
x_34 = x_680;
goto block_679;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_680;
goto block_679;
}
block_679:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_35 = lean_box(0);
x_76 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
x_104 = l_Lean_LocalDecl_isImplementationDetail(x_32);
if (x_104 == 0)
{
lean_object* x_148; uint8_t x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_168; uint8_t x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_178; uint8_t x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_269; uint8_t x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_287; uint8_t x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_306; uint8_t x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; uint8_t x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_616; 
x_148 = l_Lean_LocalDecl_type(x_32);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_148);
x_616 = l_Lean_Meta_matchNot_x3f(x_148, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
lean_dec_ref(x_616);
if (lean_obj_tag(x_617) == 1)
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
lean_dec_ref(x_617);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_619 = l_Lean_Meta_findLocalDeclWithType_x3f(x_618, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_619) == 0)
{
lean_object* x_620; 
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
lean_dec_ref(x_619);
if (lean_obj_tag(x_620) == 1)
{
lean_object* x_621; lean_object* x_622; uint8_t x_623; uint8_t x_662; 
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec_ref(x_1);
x_621 = lean_ctor_get(x_620, 0);
x_662 = !lean_is_exclusive(x_620);
if (x_662 == 0)
{
x_622 = x_620;
x_623 = x_662;
goto block_661;
}
else
{
lean_inc(x_621);
lean_dec(x_620);
x_622 = lean_box(0);
x_623 = x_662;
goto block_661;
}
block_661:
{
lean_object* x_624; 
lean_inc(x_2);
x_624 = l_Lean_MVarId_getType(x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
lean_dec_ref(x_624);
x_626 = l_Lean_LocalDecl_toExpr(x_32);
x_627 = l_Lean_mkFVar(x_621);
x_628 = l_Lean_Expr_app___override(x_626, x_627);
lean_inc(x_8);
x_629 = l_Lean_Meta_mkFalseElim(x_625, x_628, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
lean_dec_ref(x_629);
x_631 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_630, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; 
lean_dec_ref(x_631);
x_632 = lean_box(x_12);
if (x_623 == 0)
{
lean_ctor_set(x_622, 0, x_632);
x_633 = x_622;
goto block_635;
}
else
{
lean_object* x_636; 
x_636 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_636, 0, x_632);
x_633 = x_636;
goto block_635;
}
block_635:
{
lean_object* x_634; 
x_634 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_35);
x_17 = x_634;
goto block_23;
}
}
else
{
lean_object* x_637; lean_object* x_638; uint8_t x_639; uint8_t x_644; 
lean_del_object(x_622);
lean_del_object(x_15);
lean_dec(x_14);
x_637 = lean_ctor_get(x_631, 0);
x_644 = !lean_is_exclusive(x_631);
if (x_644 == 0)
{
x_638 = x_631;
x_639 = x_644;
goto block_643;
}
else
{
lean_inc(x_637);
lean_dec(x_631);
x_638 = lean_box(0);
x_639 = x_644;
goto block_643;
}
block_643:
{
lean_object* x_640; 
if (x_639 == 0)
{
x_640 = x_638;
goto block_641;
}
else
{
lean_object* x_642; 
x_642 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_642, 0, x_637);
x_640 = x_642;
goto block_641;
}
block_641:
{
return x_640;
}
}
}
}
else
{
lean_object* x_645; lean_object* x_646; uint8_t x_647; uint8_t x_652; 
lean_del_object(x_622);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
x_645 = lean_ctor_get(x_629, 0);
x_652 = !lean_is_exclusive(x_629);
if (x_652 == 0)
{
x_646 = x_629;
x_647 = x_652;
goto block_651;
}
else
{
lean_inc(x_645);
lean_dec(x_629);
x_646 = lean_box(0);
x_647 = x_652;
goto block_651;
}
block_651:
{
lean_object* x_648; 
if (x_647 == 0)
{
x_648 = x_646;
goto block_649;
}
else
{
lean_object* x_650; 
x_650 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_650, 0, x_645);
x_648 = x_650;
goto block_649;
}
block_649:
{
return x_648;
}
}
}
}
else
{
lean_object* x_653; lean_object* x_654; uint8_t x_655; uint8_t x_660; 
lean_del_object(x_622);
lean_dec(x_621);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_653 = lean_ctor_get(x_624, 0);
x_660 = !lean_is_exclusive(x_624);
if (x_660 == 0)
{
x_654 = x_624;
x_655 = x_660;
goto block_659;
}
else
{
lean_inc(x_653);
lean_dec(x_624);
x_654 = lean_box(0);
x_655 = x_660;
goto block_659;
}
block_659:
{
lean_object* x_656; 
if (x_655 == 0)
{
x_656 = x_654;
goto block_657;
}
else
{
lean_object* x_658; 
x_658 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_658, 0, x_653);
x_656 = x_658;
goto block_657;
}
block_657:
{
return x_656;
}
}
}
}
}
else
{
lean_dec(x_620);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_481 = x_7;
x_482 = x_8;
x_483 = x_9;
x_484 = x_10;
goto block_615;
}
}
else
{
lean_object* x_663; lean_object* x_664; uint8_t x_665; uint8_t x_670; 
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_663 = lean_ctor_get(x_619, 0);
x_670 = !lean_is_exclusive(x_619);
if (x_670 == 0)
{
x_664 = x_619;
x_665 = x_670;
goto block_669;
}
else
{
lean_inc(x_663);
lean_dec(x_619);
x_664 = lean_box(0);
x_665 = x_670;
goto block_669;
}
block_669:
{
lean_object* x_666; 
if (x_665 == 0)
{
x_666 = x_664;
goto block_667;
}
else
{
lean_object* x_668; 
x_668 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_668, 0, x_663);
x_666 = x_668;
goto block_667;
}
block_667:
{
return x_666;
}
}
}
}
else
{
lean_dec(x_617);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_481 = x_7;
x_482 = x_8;
x_483 = x_9;
x_484 = x_10;
goto block_615;
}
}
else
{
lean_object* x_671; lean_object* x_672; uint8_t x_673; uint8_t x_678; 
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_671 = lean_ctor_get(x_616, 0);
x_678 = !lean_is_exclusive(x_616);
if (x_678 == 0)
{
x_672 = x_616;
x_673 = x_678;
goto block_677;
}
else
{
lean_inc(x_671);
lean_dec(x_616);
x_672 = lean_box(0);
x_673 = x_678;
goto block_677;
}
block_677:
{
lean_object* x_674; 
if (x_673 == 0)
{
x_674 = x_672;
goto block_675;
}
else
{
lean_object* x_676; 
x_676 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_676, 0, x_671);
x_674 = x_676;
goto block_675;
}
block_675:
{
return x_674;
}
}
}
block_157:
{
uint8_t x_155; 
x_155 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_155 == 0)
{
lean_dec_ref(x_148);
x_126 = x_152;
x_127 = x_151;
x_128 = x_149;
x_129 = x_150;
x_130 = x_153;
x_131 = x_154;
x_132 = x_104;
goto block_147;
}
else
{
uint8_t x_156; 
x_156 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_148);
x_126 = x_152;
x_127 = x_151;
x_128 = x_149;
x_129 = x_150;
x_130 = x_153;
x_131 = x_154;
x_132 = x_156;
goto block_147;
}
}
block_167:
{
if (x_165 == 0)
{
lean_dec_ref(x_158);
x_149 = x_160;
x_150 = x_162;
x_151 = x_163;
x_152 = x_159;
x_153 = x_164;
x_154 = x_161;
goto block_157;
}
else
{
lean_object* x_166; 
lean_dec_ref(x_164);
lean_dec_ref(x_163);
lean_dec(x_161);
lean_dec(x_159);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_158);
return x_166;
}
}
block_177:
{
uint8_t x_175; 
x_175 = l_Lean_Exception_isInterrupt(x_174);
if (x_175 == 0)
{
uint8_t x_176; 
lean_inc_ref(x_174);
x_176 = l_Lean_Exception_isRuntime(x_174);
x_158 = x_174;
x_159 = x_168;
x_160 = x_169;
x_161 = x_170;
x_162 = x_171;
x_163 = x_172;
x_164 = x_173;
x_165 = x_176;
goto block_167;
}
else
{
x_158 = x_174;
x_159 = x_168;
x_160 = x_169;
x_161 = x_170;
x_162 = x_171;
x_163 = x_172;
x_164 = x_173;
x_165 = x_175;
goto block_167;
}
}
block_268:
{
lean_object* x_184; 
lean_inc(x_180);
lean_inc_ref(x_183);
lean_inc(x_178);
lean_inc_ref(x_182);
lean_inc_ref(x_148);
x_184 = l_Lean_Meta_mkDecide(x_148, x_182, x_178, x_183, x_180);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; lean_object* x_205; uint8_t x_206; uint8_t x_266; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = l_Lean_Meta_Context_config(x_182);
x_187 = lean_ctor_get_uint8(x_186, 0);
x_188 = lean_ctor_get_uint8(x_186, 1);
x_189 = lean_ctor_get_uint8(x_186, 2);
x_190 = lean_ctor_get_uint8(x_186, 3);
x_191 = lean_ctor_get_uint8(x_186, 4);
x_192 = lean_ctor_get_uint8(x_186, 5);
x_193 = lean_ctor_get_uint8(x_186, 6);
x_194 = lean_ctor_get_uint8(x_186, 7);
x_195 = lean_ctor_get_uint8(x_186, 8);
x_196 = lean_ctor_get_uint8(x_186, 10);
x_197 = lean_ctor_get_uint8(x_186, 11);
x_198 = lean_ctor_get_uint8(x_186, 12);
x_199 = lean_ctor_get_uint8(x_186, 13);
x_200 = lean_ctor_get_uint8(x_186, 14);
x_201 = lean_ctor_get_uint8(x_186, 15);
x_202 = lean_ctor_get_uint8(x_186, 16);
x_203 = lean_ctor_get_uint8(x_186, 17);
x_204 = lean_ctor_get_uint8(x_186, 18);
x_266 = !lean_is_exclusive(x_186);
if (x_266 == 0)
{
x_205 = x_186;
x_206 = x_266;
goto block_265;
}
else
{
lean_dec(x_186);
x_205 = lean_box(0);
x_206 = x_266;
goto block_265;
}
block_265:
{
uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; lean_object* x_218; 
x_207 = lean_ctor_get_uint8(x_182, sizeof(void*)*7);
x_208 = lean_ctor_get(x_182, 1);
x_209 = lean_ctor_get(x_182, 2);
x_210 = lean_ctor_get(x_182, 3);
x_211 = lean_ctor_get(x_182, 4);
x_212 = lean_ctor_get(x_182, 5);
x_213 = lean_ctor_get(x_182, 6);
x_214 = lean_ctor_get_uint8(x_182, sizeof(void*)*7 + 1);
x_215 = lean_ctor_get_uint8(x_182, sizeof(void*)*7 + 2);
x_216 = lean_ctor_get_uint8(x_182, sizeof(void*)*7 + 3);
x_217 = 1;
if (x_206 == 0)
{
x_218 = x_205;
goto block_263;
}
else
{
lean_object* x_264; 
x_264 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_264, 0, x_187);
lean_ctor_set_uint8(x_264, 1, x_188);
lean_ctor_set_uint8(x_264, 2, x_189);
lean_ctor_set_uint8(x_264, 3, x_190);
lean_ctor_set_uint8(x_264, 4, x_191);
lean_ctor_set_uint8(x_264, 5, x_192);
lean_ctor_set_uint8(x_264, 6, x_193);
lean_ctor_set_uint8(x_264, 7, x_194);
lean_ctor_set_uint8(x_264, 8, x_195);
lean_ctor_set_uint8(x_264, 10, x_196);
lean_ctor_set_uint8(x_264, 11, x_197);
lean_ctor_set_uint8(x_264, 12, x_198);
lean_ctor_set_uint8(x_264, 13, x_199);
lean_ctor_set_uint8(x_264, 14, x_200);
lean_ctor_set_uint8(x_264, 15, x_201);
lean_ctor_set_uint8(x_264, 16, x_202);
lean_ctor_set_uint8(x_264, 17, x_203);
lean_ctor_set_uint8(x_264, 18, x_204);
x_218 = x_264;
goto block_263;
}
block_263:
{
uint64_t x_219; uint64_t x_220; uint64_t x_221; uint64_t x_222; uint64_t x_223; uint64_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_ctor_set_uint8(x_218, 9, x_217);
x_219 = l_Lean_Meta_Context_configKey(x_182);
x_220 = 2;
x_221 = lean_uint64_shift_right(x_219, x_220);
x_222 = lean_uint64_shift_left(x_221, x_220);
x_223 = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
x_224 = lean_uint64_lor(x_222, x_223);
x_225 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_225, 0, x_218);
lean_ctor_set_uint64(x_225, sizeof(void*)*1, x_224);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc_ref(x_210);
lean_inc_ref(x_209);
lean_inc(x_208);
x_226 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_208);
lean_ctor_set(x_226, 2, x_209);
lean_ctor_set(x_226, 3, x_210);
lean_ctor_set(x_226, 4, x_211);
lean_ctor_set(x_226, 5, x_212);
lean_ctor_set(x_226, 6, x_213);
lean_ctor_set_uint8(x_226, sizeof(void*)*7, x_207);
lean_ctor_set_uint8(x_226, sizeof(void*)*7 + 1, x_214);
lean_ctor_set_uint8(x_226, sizeof(void*)*7 + 2, x_215);
lean_ctor_set_uint8(x_226, sizeof(void*)*7 + 3, x_216);
lean_inc(x_180);
lean_inc_ref(x_183);
lean_inc(x_178);
lean_inc(x_185);
x_227 = lean_whnf(x_185, x_226, x_178, x_183, x_180);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec_ref(x_227);
x_229 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
x_230 = l_Lean_Expr_isConstOf(x_228, x_229);
lean_dec(x_228);
if (x_230 == 0)
{
lean_dec(x_185);
x_149 = x_179;
x_150 = x_181;
x_151 = x_182;
x_152 = x_178;
x_153 = x_183;
x_154 = x_180;
goto block_157;
}
else
{
lean_object* x_231; 
lean_inc(x_180);
lean_inc_ref(x_183);
lean_inc(x_178);
lean_inc_ref(x_182);
lean_inc(x_185);
x_231 = l_Lean_Meta_mkEqRefl(x_185, x_182, x_178, x_183, x_180);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec_ref(x_231);
lean_inc(x_2);
x_233 = l_Lean_MVarId_getType(x_2, x_182, x_178, x_183, x_180);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
lean_dec_ref(x_233);
x_235 = l_Lean_Expr_getAppNumArgs(x_185);
x_236 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
x_237 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(x_235);
x_238 = lean_mk_array(x_235, x_237);
x_239 = lean_unsigned_to_nat(1u);
x_240 = lean_nat_sub(x_235, x_239);
lean_dec(x_235);
x_241 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_185, x_238, x_240);
x_242 = lean_array_push(x_241, x_232);
x_243 = l_Lean_mkAppN(x_236, x_242);
lean_dec_ref(x_242);
lean_inc(x_32);
x_244 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_180);
lean_inc_ref(x_183);
lean_inc(x_178);
lean_inc_ref(x_182);
x_245 = l_Lean_Meta_mkAbsurd(x_234, x_244, x_243, x_182, x_178, x_183, x_180);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
lean_inc(x_2);
x_247 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_246, x_178);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; uint8_t x_249; uint8_t x_256; 
lean_dec_ref(x_183);
lean_dec_ref(x_182);
lean_dec(x_180);
lean_dec(x_178);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_256 = !lean_is_exclusive(x_247);
if (x_256 == 0)
{
lean_object* x_257; 
x_257 = lean_ctor_get(x_247, 0);
lean_dec(x_257);
x_248 = x_247;
x_249 = x_256;
goto block_255;
}
else
{
lean_dec(x_247);
x_248 = lean_box(0);
x_249 = x_256;
goto block_255;
}
block_255:
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_box(x_12);
if (x_249 == 0)
{
lean_ctor_set_tag(x_248, 1);
lean_ctor_set(x_248, 0, x_250);
x_251 = x_248;
goto block_253;
}
else
{
lean_object* x_254; 
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_250);
x_251 = x_254;
goto block_253;
}
block_253:
{
lean_object* x_252; 
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_35);
x_17 = x_252;
goto block_23;
}
}
}
else
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_247, 0);
lean_inc(x_258);
lean_dec_ref(x_247);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_258;
goto block_177;
}
}
else
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_245, 0);
lean_inc(x_259);
lean_dec_ref(x_245);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_259;
goto block_177;
}
}
else
{
lean_object* x_260; 
lean_dec(x_232);
lean_dec(x_185);
x_260 = lean_ctor_get(x_233, 0);
lean_inc(x_260);
lean_dec_ref(x_233);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_260;
goto block_177;
}
}
else
{
lean_object* x_261; 
lean_dec(x_185);
x_261 = lean_ctor_get(x_231, 0);
lean_inc(x_261);
lean_dec_ref(x_231);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_261;
goto block_177;
}
}
}
else
{
lean_object* x_262; 
lean_dec(x_185);
x_262 = lean_ctor_get(x_227, 0);
lean_inc(x_262);
lean_dec_ref(x_227);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_262;
goto block_177;
}
}
}
}
else
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_184, 0);
lean_inc(x_267);
lean_dec_ref(x_184);
x_168 = x_178;
x_169 = x_179;
x_170 = x_180;
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_267;
goto block_177;
}
}
block_276:
{
if (x_275 == 0)
{
x_149 = x_270;
x_150 = x_272;
x_151 = x_273;
x_152 = x_269;
x_153 = x_274;
x_154 = x_271;
goto block_157;
}
else
{
x_178 = x_269;
x_179 = x_270;
x_180 = x_271;
x_181 = x_272;
x_182 = x_273;
x_183 = x_274;
goto block_268;
}
}
block_286:
{
if (x_284 == 0)
{
lean_dec_ref(x_277);
x_269 = x_278;
x_270 = x_279;
x_271 = x_280;
x_272 = x_281;
x_273 = x_282;
x_274 = x_283;
x_275 = x_104;
goto block_276;
}
else
{
uint8_t x_285; 
x_285 = l_Lean_Expr_hasFVar(x_277);
lean_dec_ref(x_277);
if (x_285 == 0)
{
x_178 = x_278;
x_179 = x_279;
x_180 = x_280;
x_181 = x_281;
x_182 = x_282;
x_183 = x_283;
goto block_268;
}
else
{
x_269 = x_278;
x_270 = x_279;
x_271 = x_280;
x_272 = x_281;
x_273 = x_282;
x_274 = x_283;
x_275 = x_104;
goto block_276;
}
}
}
block_305:
{
lean_object* x_294; 
lean_inc_ref(x_148);
x_294 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_148, x_287);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; uint8_t x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec_ref(x_294);
x_296 = l_Lean_Expr_hasMVar(x_295);
if (x_296 == 0)
{
x_277 = x_295;
x_278 = x_287;
x_279 = x_288;
x_280 = x_289;
x_281 = x_290;
x_282 = x_291;
x_283 = x_292;
x_284 = x_293;
goto block_286;
}
else
{
x_277 = x_295;
x_278 = x_287;
x_279 = x_288;
x_280 = x_289;
x_281 = x_290;
x_282 = x_291;
x_283 = x_292;
x_284 = x_104;
goto block_286;
}
}
else
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; uint8_t x_304; 
lean_dec_ref(x_292);
lean_dec_ref(x_291);
lean_dec(x_289);
lean_dec(x_287);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_297 = lean_ctor_get(x_294, 0);
x_304 = !lean_is_exclusive(x_294);
if (x_304 == 0)
{
x_298 = x_294;
x_299 = x_304;
goto block_303;
}
else
{
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_box(0);
x_299 = x_304;
goto block_303;
}
block_303:
{
lean_object* x_300; 
if (x_299 == 0)
{
x_300 = x_298;
goto block_301;
}
else
{
lean_object* x_302; 
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_297);
x_300 = x_302;
goto block_301;
}
block_301:
{
return x_300;
}
}
}
}
block_313:
{
if (x_312 == 0)
{
x_149 = x_307;
x_150 = x_309;
x_151 = x_310;
x_152 = x_306;
x_153 = x_311;
x_154 = x_308;
goto block_157;
}
else
{
x_287 = x_306;
x_288 = x_307;
x_289 = x_308;
x_290 = x_309;
x_291 = x_310;
x_292 = x_311;
x_293 = x_312;
goto block_305;
}
}
block_322:
{
uint8_t x_320; 
x_320 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_320 == 0)
{
x_306 = x_317;
x_307 = x_315;
x_308 = x_319;
x_309 = x_314;
x_310 = x_316;
x_311 = x_318;
x_312 = x_104;
goto block_313;
}
else
{
uint8_t x_321; 
x_321 = l_Lean_Expr_hasFVar(x_148);
if (x_321 == 0)
{
x_287 = x_317;
x_288 = x_315;
x_289 = x_319;
x_290 = x_314;
x_291 = x_316;
x_292 = x_318;
x_293 = x_320;
goto block_305;
}
else
{
x_306 = x_317;
x_307 = x_315;
x_308 = x_319;
x_309 = x_314;
x_310 = x_316;
x_311 = x_318;
x_312 = x_104;
goto block_313;
}
}
}
block_384:
{
lean_object* x_330; 
lean_inc(x_324);
lean_inc_ref(x_325);
lean_inc(x_329);
lean_inc_ref(x_323);
x_330 = l_Lean_Meta_isExprDefEq(x_327, x_326, x_323, x_329, x_325, x_324);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; uint8_t x_332; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
lean_dec_ref(x_330);
x_332 = lean_unbox(x_331);
lean_dec(x_331);
if (x_332 == 0)
{
x_314 = x_328;
x_315 = x_12;
x_316 = x_323;
x_317 = x_329;
x_318 = x_325;
x_319 = x_324;
goto block_322;
}
else
{
lean_object* x_333; 
lean_dec_ref(x_148);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_333 = l_Lean_MVarId_getType(x_2, x_323, x_329, x_325, x_324);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
lean_dec_ref(x_333);
x_335 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_324);
lean_inc_ref(x_325);
lean_inc(x_329);
lean_inc_ref(x_323);
x_336 = l_Lean_Meta_mkEqOfHEq(x_335, x_12, x_323, x_329, x_325, x_324);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
lean_dec_ref(x_336);
lean_inc(x_329);
x_338 = l_Lean_Meta_mkNoConfusion(x_334, x_337, x_323, x_329, x_325, x_324);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_340 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_339, x_329);
lean_dec(x_329);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec_ref(x_340);
x_341 = lean_box(x_12);
x_342 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_342, 0, x_341);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_35);
x_17 = x_343;
goto block_23;
}
else
{
lean_object* x_344; lean_object* x_345; uint8_t x_346; uint8_t x_351; 
lean_del_object(x_15);
lean_dec(x_14);
x_344 = lean_ctor_get(x_340, 0);
x_351 = !lean_is_exclusive(x_340);
if (x_351 == 0)
{
x_345 = x_340;
x_346 = x_351;
goto block_350;
}
else
{
lean_inc(x_344);
lean_dec(x_340);
x_345 = lean_box(0);
x_346 = x_351;
goto block_350;
}
block_350:
{
lean_object* x_347; 
if (x_346 == 0)
{
x_347 = x_345;
goto block_348;
}
else
{
lean_object* x_349; 
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_344);
x_347 = x_349;
goto block_348;
}
block_348:
{
return x_347;
}
}
}
}
else
{
lean_object* x_352; lean_object* x_353; uint8_t x_354; uint8_t x_359; 
lean_dec(x_329);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_352 = lean_ctor_get(x_338, 0);
x_359 = !lean_is_exclusive(x_338);
if (x_359 == 0)
{
x_353 = x_338;
x_354 = x_359;
goto block_358;
}
else
{
lean_inc(x_352);
lean_dec(x_338);
x_353 = lean_box(0);
x_354 = x_359;
goto block_358;
}
block_358:
{
lean_object* x_355; 
if (x_354 == 0)
{
x_355 = x_353;
goto block_356;
}
else
{
lean_object* x_357; 
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_352);
x_355 = x_357;
goto block_356;
}
block_356:
{
return x_355;
}
}
}
}
else
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_367; 
lean_dec(x_334);
lean_dec(x_329);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_360 = lean_ctor_get(x_336, 0);
x_367 = !lean_is_exclusive(x_336);
if (x_367 == 0)
{
x_361 = x_336;
x_362 = x_367;
goto block_366;
}
else
{
lean_inc(x_360);
lean_dec(x_336);
x_361 = lean_box(0);
x_362 = x_367;
goto block_366;
}
block_366:
{
lean_object* x_363; 
if (x_362 == 0)
{
x_363 = x_361;
goto block_364;
}
else
{
lean_object* x_365; 
x_365 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_365, 0, x_360);
x_363 = x_365;
goto block_364;
}
block_364:
{
return x_363;
}
}
}
}
else
{
lean_object* x_368; lean_object* x_369; uint8_t x_370; uint8_t x_375; 
lean_dec(x_329);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_368 = lean_ctor_get(x_333, 0);
x_375 = !lean_is_exclusive(x_333);
if (x_375 == 0)
{
x_369 = x_333;
x_370 = x_375;
goto block_374;
}
else
{
lean_inc(x_368);
lean_dec(x_333);
x_369 = lean_box(0);
x_370 = x_375;
goto block_374;
}
block_374:
{
lean_object* x_371; 
if (x_370 == 0)
{
x_371 = x_369;
goto block_372;
}
else
{
lean_object* x_373; 
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_368);
x_371 = x_373;
goto block_372;
}
block_372:
{
return x_371;
}
}
}
}
}
else
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; uint8_t x_383; 
lean_dec(x_329);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_376 = lean_ctor_get(x_330, 0);
x_383 = !lean_is_exclusive(x_330);
if (x_383 == 0)
{
x_377 = x_330;
x_378 = x_383;
goto block_382;
}
else
{
lean_inc(x_376);
lean_dec(x_330);
x_377 = lean_box(0);
x_378 = x_383;
goto block_382;
}
block_382:
{
lean_object* x_379; 
if (x_378 == 0)
{
x_379 = x_377;
goto block_380;
}
else
{
lean_object* x_381; 
x_381 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_381, 0, x_376);
x_379 = x_381;
goto block_380;
}
block_380:
{
return x_379;
}
}
}
}
block_434:
{
lean_object* x_390; 
lean_inc(x_389);
lean_inc_ref(x_388);
lean_inc(x_387);
lean_inc_ref(x_386);
lean_inc_ref(x_148);
x_390 = l_Lean_Meta_matchHEq_x3f(x_148, x_386, x_387, x_388, x_389);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec_ref(x_390);
if (lean_obj_tag(x_391) == 1)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
lean_dec_ref(x_391);
x_393 = lean_ctor_get(x_392, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_393, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_392, 0);
lean_inc(x_395);
lean_dec(x_392);
x_396 = lean_ctor_get(x_393, 0);
lean_inc(x_396);
lean_dec(x_393);
x_397 = lean_ctor_get(x_394, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_394, 1);
lean_inc(x_398);
lean_dec(x_394);
lean_inc(x_389);
lean_inc_ref(x_388);
lean_inc(x_387);
lean_inc_ref(x_386);
x_399 = l_Lean_Meta_matchConstructorApp_x3f(x_396, x_386, x_387, x_388, x_389);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
lean_dec_ref(x_399);
if (lean_obj_tag(x_400) == 1)
{
lean_object* x_401; lean_object* x_402; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec_ref(x_400);
lean_inc(x_389);
lean_inc_ref(x_388);
lean_inc(x_387);
lean_inc_ref(x_386);
x_402 = l_Lean_Meta_matchConstructorApp_x3f(x_398, x_386, x_387, x_388, x_389);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
lean_dec_ref(x_402);
if (lean_obj_tag(x_403) == 1)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_404 = lean_ctor_get(x_401, 0);
lean_inc_ref(x_404);
lean_dec(x_401);
x_405 = lean_ctor_get(x_403, 0);
lean_inc(x_405);
lean_dec_ref(x_403);
x_406 = lean_ctor_get(x_405, 0);
lean_inc_ref(x_406);
lean_dec(x_405);
x_407 = lean_ctor_get(x_404, 0);
lean_inc(x_407);
lean_dec_ref(x_404);
x_408 = lean_ctor_get(x_406, 0);
lean_inc(x_408);
lean_dec_ref(x_406);
x_409 = lean_name_eq(x_407, x_408);
lean_dec(x_408);
lean_dec(x_407);
if (x_409 == 0)
{
x_323 = x_386;
x_324 = x_389;
x_325 = x_388;
x_326 = x_397;
x_327 = x_395;
x_328 = x_385;
x_329 = x_387;
goto block_384;
}
else
{
if (x_104 == 0)
{
lean_dec(x_397);
lean_dec(x_395);
x_314 = x_385;
x_315 = x_12;
x_316 = x_386;
x_317 = x_387;
x_318 = x_388;
x_319 = x_389;
goto block_322;
}
else
{
x_323 = x_386;
x_324 = x_389;
x_325 = x_388;
x_326 = x_397;
x_327 = x_395;
x_328 = x_385;
x_329 = x_387;
goto block_384;
}
}
}
else
{
lean_dec(x_403);
lean_dec(x_401);
lean_dec(x_397);
lean_dec(x_395);
x_314 = x_385;
x_315 = x_12;
x_316 = x_386;
x_317 = x_387;
x_318 = x_388;
x_319 = x_389;
goto block_322;
}
}
else
{
lean_object* x_410; lean_object* x_411; uint8_t x_412; uint8_t x_417; 
lean_dec(x_401);
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_389);
lean_dec_ref(x_388);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_410 = lean_ctor_get(x_402, 0);
x_417 = !lean_is_exclusive(x_402);
if (x_417 == 0)
{
x_411 = x_402;
x_412 = x_417;
goto block_416;
}
else
{
lean_inc(x_410);
lean_dec(x_402);
x_411 = lean_box(0);
x_412 = x_417;
goto block_416;
}
block_416:
{
lean_object* x_413; 
if (x_412 == 0)
{
x_413 = x_411;
goto block_414;
}
else
{
lean_object* x_415; 
x_415 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_415, 0, x_410);
x_413 = x_415;
goto block_414;
}
block_414:
{
return x_413;
}
}
}
}
else
{
lean_dec(x_400);
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_395);
x_314 = x_385;
x_315 = x_12;
x_316 = x_386;
x_317 = x_387;
x_318 = x_388;
x_319 = x_389;
goto block_322;
}
}
else
{
lean_object* x_418; lean_object* x_419; uint8_t x_420; uint8_t x_425; 
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_395);
lean_dec(x_389);
lean_dec_ref(x_388);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_418 = lean_ctor_get(x_399, 0);
x_425 = !lean_is_exclusive(x_399);
if (x_425 == 0)
{
x_419 = x_399;
x_420 = x_425;
goto block_424;
}
else
{
lean_inc(x_418);
lean_dec(x_399);
x_419 = lean_box(0);
x_420 = x_425;
goto block_424;
}
block_424:
{
lean_object* x_421; 
if (x_420 == 0)
{
x_421 = x_419;
goto block_422;
}
else
{
lean_object* x_423; 
x_423 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_423, 0, x_418);
x_421 = x_423;
goto block_422;
}
block_422:
{
return x_421;
}
}
}
}
else
{
lean_dec(x_391);
x_314 = x_385;
x_315 = x_104;
x_316 = x_386;
x_317 = x_387;
x_318 = x_388;
x_319 = x_389;
goto block_322;
}
}
else
{
lean_object* x_426; lean_object* x_427; uint8_t x_428; uint8_t x_433; 
lean_dec(x_389);
lean_dec_ref(x_388);
lean_dec(x_387);
lean_dec_ref(x_386);
lean_dec_ref(x_148);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_426 = lean_ctor_get(x_390, 0);
x_433 = !lean_is_exclusive(x_390);
if (x_433 == 0)
{
x_427 = x_390;
x_428 = x_433;
goto block_432;
}
else
{
lean_inc(x_426);
lean_dec(x_390);
x_427 = lean_box(0);
x_428 = x_433;
goto block_432;
}
block_432:
{
lean_object* x_429; 
if (x_428 == 0)
{
x_429 = x_427;
goto block_430;
}
else
{
lean_object* x_431; 
x_431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_431, 0, x_426);
x_429 = x_431;
goto block_430;
}
block_430:
{
return x_429;
}
}
}
}
block_480:
{
lean_object* x_439; 
lean_inc(x_438);
lean_inc_ref(x_437);
lean_inc(x_436);
lean_inc_ref(x_435);
lean_inc_ref(x_148);
x_439 = l_Lean_Meta_matchEq_x3f(x_148, x_435, x_436, x_437, x_438);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
lean_dec_ref(x_439);
if (lean_obj_tag(x_440) == 1)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
lean_dec_ref(x_440);
x_442 = lean_ctor_get(x_441, 1);
lean_inc(x_442);
lean_dec(x_441);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
lean_inc(x_438);
lean_inc_ref(x_437);
lean_inc(x_436);
lean_inc_ref(x_435);
x_445 = l_Lean_Meta_matchConstructorApp_x3f(x_443, x_435, x_436, x_437, x_438);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
lean_dec_ref(x_445);
if (lean_obj_tag(x_446) == 1)
{
lean_object* x_447; lean_object* x_448; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
lean_dec_ref(x_446);
lean_inc(x_438);
lean_inc_ref(x_437);
lean_inc(x_436);
lean_inc_ref(x_435);
x_448 = l_Lean_Meta_matchConstructorApp_x3f(x_444, x_435, x_436, x_437, x_438);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
lean_dec_ref(x_448);
if (lean_obj_tag(x_449) == 1)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; 
x_450 = lean_ctor_get(x_447, 0);
lean_inc_ref(x_450);
lean_dec(x_447);
x_451 = lean_ctor_get(x_449, 0);
lean_inc(x_451);
lean_dec_ref(x_449);
x_452 = lean_ctor_get(x_451, 0);
lean_inc_ref(x_452);
lean_dec(x_451);
x_453 = lean_ctor_get(x_450, 0);
lean_inc(x_453);
lean_dec_ref(x_450);
x_454 = lean_ctor_get(x_452, 0);
lean_inc(x_454);
lean_dec_ref(x_452);
x_455 = lean_name_eq(x_453, x_454);
lean_dec(x_454);
lean_dec(x_453);
if (x_455 == 0)
{
lean_dec_ref(x_148);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_36 = x_437;
x_37 = x_438;
x_38 = x_435;
x_39 = x_436;
goto block_75;
}
else
{
if (x_104 == 0)
{
lean_del_object(x_33);
x_385 = x_12;
x_386 = x_435;
x_387 = x_436;
x_388 = x_437;
x_389 = x_438;
goto block_434;
}
else
{
lean_dec_ref(x_148);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_36 = x_437;
x_37 = x_438;
x_38 = x_435;
x_39 = x_436;
goto block_75;
}
}
}
else
{
lean_dec(x_449);
lean_dec(x_447);
lean_del_object(x_33);
x_385 = x_12;
x_386 = x_435;
x_387 = x_436;
x_388 = x_437;
x_389 = x_438;
goto block_434;
}
}
else
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; uint8_t x_463; 
lean_dec(x_447);
lean_dec(x_438);
lean_dec_ref(x_437);
lean_dec(x_436);
lean_dec_ref(x_435);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_456 = lean_ctor_get(x_448, 0);
x_463 = !lean_is_exclusive(x_448);
if (x_463 == 0)
{
x_457 = x_448;
x_458 = x_463;
goto block_462;
}
else
{
lean_inc(x_456);
lean_dec(x_448);
x_457 = lean_box(0);
x_458 = x_463;
goto block_462;
}
block_462:
{
lean_object* x_459; 
if (x_458 == 0)
{
x_459 = x_457;
goto block_460;
}
else
{
lean_object* x_461; 
x_461 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_461, 0, x_456);
x_459 = x_461;
goto block_460;
}
block_460:
{
return x_459;
}
}
}
}
else
{
lean_dec(x_446);
lean_dec(x_444);
lean_del_object(x_33);
x_385 = x_12;
x_386 = x_435;
x_387 = x_436;
x_388 = x_437;
x_389 = x_438;
goto block_434;
}
}
else
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; uint8_t x_471; 
lean_dec(x_444);
lean_dec(x_438);
lean_dec_ref(x_437);
lean_dec(x_436);
lean_dec_ref(x_435);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_464 = lean_ctor_get(x_445, 0);
x_471 = !lean_is_exclusive(x_445);
if (x_471 == 0)
{
x_465 = x_445;
x_466 = x_471;
goto block_470;
}
else
{
lean_inc(x_464);
lean_dec(x_445);
x_465 = lean_box(0);
x_466 = x_471;
goto block_470;
}
block_470:
{
lean_object* x_467; 
if (x_466 == 0)
{
x_467 = x_465;
goto block_468;
}
else
{
lean_object* x_469; 
x_469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_469, 0, x_464);
x_467 = x_469;
goto block_468;
}
block_468:
{
return x_467;
}
}
}
}
else
{
lean_dec(x_440);
lean_del_object(x_33);
x_385 = x_104;
x_386 = x_435;
x_387 = x_436;
x_388 = x_437;
x_389 = x_438;
goto block_434;
}
}
else
{
lean_object* x_472; lean_object* x_473; uint8_t x_474; uint8_t x_479; 
lean_dec(x_438);
lean_dec_ref(x_437);
lean_dec(x_436);
lean_dec_ref(x_435);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_472 = lean_ctor_get(x_439, 0);
x_479 = !lean_is_exclusive(x_439);
if (x_479 == 0)
{
x_473 = x_439;
x_474 = x_479;
goto block_478;
}
else
{
lean_inc(x_472);
lean_dec(x_439);
x_473 = lean_box(0);
x_474 = x_479;
goto block_478;
}
block_478:
{
lean_object* x_475; 
if (x_474 == 0)
{
x_475 = x_473;
goto block_476;
}
else
{
lean_object* x_477; 
x_477 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_477, 0, x_472);
x_475 = x_477;
goto block_476;
}
block_476:
{
return x_475;
}
}
}
}
block_615:
{
lean_object* x_485; 
lean_inc(x_484);
lean_inc_ref(x_483);
lean_inc(x_482);
lean_inc_ref(x_481);
lean_inc_ref(x_148);
x_485 = l_refutableHasNotBit_x3f(x_148, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
lean_dec_ref(x_485);
if (lean_obj_tag(x_486) == 1)
{
lean_object* x_487; lean_object* x_488; uint8_t x_489; uint8_t x_526; 
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_487 = lean_ctor_get(x_486, 0);
x_526 = !lean_is_exclusive(x_486);
if (x_526 == 0)
{
x_488 = x_486;
x_489 = x_526;
goto block_525;
}
else
{
lean_inc(x_487);
lean_dec(x_486);
x_488 = lean_box(0);
x_489 = x_526;
goto block_525;
}
block_525:
{
lean_object* x_490; 
lean_inc(x_2);
x_490 = l_Lean_MVarId_getType(x_2, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
lean_dec_ref(x_490);
x_492 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_482);
x_493 = l_Lean_Meta_mkAbsurd(x_491, x_487, x_492, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
lean_dec_ref(x_493);
x_495 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_494, x_482);
lean_dec(x_482);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; 
lean_dec_ref(x_495);
x_496 = lean_box(x_12);
if (x_489 == 0)
{
lean_ctor_set(x_488, 0, x_496);
x_497 = x_488;
goto block_499;
}
else
{
lean_object* x_500; 
x_500 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_500, 0, x_496);
x_497 = x_500;
goto block_499;
}
block_499:
{
lean_object* x_498; 
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_35);
x_17 = x_498;
goto block_23;
}
}
else
{
lean_object* x_501; lean_object* x_502; uint8_t x_503; uint8_t x_508; 
lean_del_object(x_488);
lean_del_object(x_15);
lean_dec(x_14);
x_501 = lean_ctor_get(x_495, 0);
x_508 = !lean_is_exclusive(x_495);
if (x_508 == 0)
{
x_502 = x_495;
x_503 = x_508;
goto block_507;
}
else
{
lean_inc(x_501);
lean_dec(x_495);
x_502 = lean_box(0);
x_503 = x_508;
goto block_507;
}
block_507:
{
lean_object* x_504; 
if (x_503 == 0)
{
x_504 = x_502;
goto block_505;
}
else
{
lean_object* x_506; 
x_506 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_506, 0, x_501);
x_504 = x_506;
goto block_505;
}
block_505:
{
return x_504;
}
}
}
}
else
{
lean_object* x_509; lean_object* x_510; uint8_t x_511; uint8_t x_516; 
lean_del_object(x_488);
lean_dec(x_482);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_509 = lean_ctor_get(x_493, 0);
x_516 = !lean_is_exclusive(x_493);
if (x_516 == 0)
{
x_510 = x_493;
x_511 = x_516;
goto block_515;
}
else
{
lean_inc(x_509);
lean_dec(x_493);
x_510 = lean_box(0);
x_511 = x_516;
goto block_515;
}
block_515:
{
lean_object* x_512; 
if (x_511 == 0)
{
x_512 = x_510;
goto block_513;
}
else
{
lean_object* x_514; 
x_514 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_514, 0, x_509);
x_512 = x_514;
goto block_513;
}
block_513:
{
return x_512;
}
}
}
}
else
{
lean_object* x_517; lean_object* x_518; uint8_t x_519; uint8_t x_524; 
lean_del_object(x_488);
lean_dec(x_487);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_517 = lean_ctor_get(x_490, 0);
x_524 = !lean_is_exclusive(x_490);
if (x_524 == 0)
{
x_518 = x_490;
x_519 = x_524;
goto block_523;
}
else
{
lean_inc(x_517);
lean_dec(x_490);
x_518 = lean_box(0);
x_519 = x_524;
goto block_523;
}
block_523:
{
lean_object* x_520; 
if (x_519 == 0)
{
x_520 = x_518;
goto block_521;
}
else
{
lean_object* x_522; 
x_522 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_522, 0, x_517);
x_520 = x_522;
goto block_521;
}
block_521:
{
return x_520;
}
}
}
}
}
else
{
lean_object* x_527; 
lean_dec(x_486);
lean_inc(x_484);
lean_inc_ref(x_483);
lean_inc(x_482);
lean_inc_ref(x_481);
lean_inc_ref(x_148);
x_527 = l_Lean_Meta_matchNe_x3f(x_148, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
lean_dec_ref(x_527);
if (lean_obj_tag(x_528) == 1)
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; uint8_t x_598; 
x_529 = lean_ctor_get(x_528, 0);
x_598 = !lean_is_exclusive(x_528);
if (x_598 == 0)
{
x_530 = x_528;
x_531 = x_598;
goto block_597;
}
else
{
lean_inc(x_529);
lean_dec(x_528);
x_530 = lean_box(0);
x_531 = x_598;
goto block_597;
}
block_597:
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; uint8_t x_596; 
x_532 = lean_ctor_get(x_529, 1);
lean_inc(x_532);
lean_dec(x_529);
x_533 = lean_ctor_get(x_532, 0);
x_534 = lean_ctor_get(x_532, 1);
x_596 = !lean_is_exclusive(x_532);
if (x_596 == 0)
{
x_535 = x_532;
x_536 = x_596;
goto block_595;
}
else
{
lean_inc(x_534);
lean_inc(x_533);
lean_dec(x_532);
x_535 = lean_box(0);
x_536 = x_596;
goto block_595;
}
block_595:
{
lean_object* x_537; 
lean_inc(x_484);
lean_inc_ref(x_483);
lean_inc(x_482);
lean_inc_ref(x_481);
lean_inc(x_533);
x_537 = l_Lean_Meta_isExprDefEq(x_533, x_534, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; uint8_t x_539; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
lean_dec_ref(x_537);
x_539 = lean_unbox(x_538);
lean_dec(x_538);
if (x_539 == 0)
{
lean_del_object(x_535);
lean_dec(x_533);
lean_del_object(x_530);
x_435 = x_481;
x_436 = x_482;
x_437 = x_483;
x_438 = x_484;
goto block_480;
}
else
{
lean_object* x_540; 
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_540 = l_Lean_MVarId_getType(x_2, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; 
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
lean_dec_ref(x_540);
lean_inc(x_484);
lean_inc_ref(x_483);
lean_inc(x_482);
lean_inc_ref(x_481);
x_542 = l_Lean_Meta_mkEqRefl(x_533, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
lean_dec_ref(x_542);
x_544 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_482);
x_545 = l_Lean_Meta_mkAbsurd(x_541, x_543, x_544, x_481, x_482, x_483, x_484);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
lean_dec_ref(x_545);
x_547 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_546, x_482);
lean_dec(x_482);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; 
lean_dec_ref(x_547);
x_548 = lean_box(x_12);
if (x_531 == 0)
{
lean_ctor_set(x_530, 0, x_548);
x_549 = x_530;
goto block_553;
}
else
{
lean_object* x_554; 
x_554 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_554, 0, x_548);
x_549 = x_554;
goto block_553;
}
block_553:
{
lean_object* x_550; 
if (x_536 == 0)
{
lean_ctor_set(x_535, 1, x_35);
lean_ctor_set(x_535, 0, x_549);
x_550 = x_535;
goto block_551;
}
else
{
lean_object* x_552; 
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_549);
lean_ctor_set(x_552, 1, x_35);
x_550 = x_552;
goto block_551;
}
block_551:
{
x_17 = x_550;
goto block_23;
}
}
}
else
{
lean_object* x_555; lean_object* x_556; uint8_t x_557; uint8_t x_562; 
lean_del_object(x_535);
lean_del_object(x_530);
lean_del_object(x_15);
lean_dec(x_14);
x_555 = lean_ctor_get(x_547, 0);
x_562 = !lean_is_exclusive(x_547);
if (x_562 == 0)
{
x_556 = x_547;
x_557 = x_562;
goto block_561;
}
else
{
lean_inc(x_555);
lean_dec(x_547);
x_556 = lean_box(0);
x_557 = x_562;
goto block_561;
}
block_561:
{
lean_object* x_558; 
if (x_557 == 0)
{
x_558 = x_556;
goto block_559;
}
else
{
lean_object* x_560; 
x_560 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_560, 0, x_555);
x_558 = x_560;
goto block_559;
}
block_559:
{
return x_558;
}
}
}
}
else
{
lean_object* x_563; lean_object* x_564; uint8_t x_565; uint8_t x_570; 
lean_del_object(x_535);
lean_del_object(x_530);
lean_dec(x_482);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_563 = lean_ctor_get(x_545, 0);
x_570 = !lean_is_exclusive(x_545);
if (x_570 == 0)
{
x_564 = x_545;
x_565 = x_570;
goto block_569;
}
else
{
lean_inc(x_563);
lean_dec(x_545);
x_564 = lean_box(0);
x_565 = x_570;
goto block_569;
}
block_569:
{
lean_object* x_566; 
if (x_565 == 0)
{
x_566 = x_564;
goto block_567;
}
else
{
lean_object* x_568; 
x_568 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_568, 0, x_563);
x_566 = x_568;
goto block_567;
}
block_567:
{
return x_566;
}
}
}
}
else
{
lean_object* x_571; lean_object* x_572; uint8_t x_573; uint8_t x_578; 
lean_dec(x_541);
lean_del_object(x_535);
lean_del_object(x_530);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_571 = lean_ctor_get(x_542, 0);
x_578 = !lean_is_exclusive(x_542);
if (x_578 == 0)
{
x_572 = x_542;
x_573 = x_578;
goto block_577;
}
else
{
lean_inc(x_571);
lean_dec(x_542);
x_572 = lean_box(0);
x_573 = x_578;
goto block_577;
}
block_577:
{
lean_object* x_574; 
if (x_573 == 0)
{
x_574 = x_572;
goto block_575;
}
else
{
lean_object* x_576; 
x_576 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_576, 0, x_571);
x_574 = x_576;
goto block_575;
}
block_575:
{
return x_574;
}
}
}
}
else
{
lean_object* x_579; lean_object* x_580; uint8_t x_581; uint8_t x_586; 
lean_del_object(x_535);
lean_dec(x_533);
lean_del_object(x_530);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_579 = lean_ctor_get(x_540, 0);
x_586 = !lean_is_exclusive(x_540);
if (x_586 == 0)
{
x_580 = x_540;
x_581 = x_586;
goto block_585;
}
else
{
lean_inc(x_579);
lean_dec(x_540);
x_580 = lean_box(0);
x_581 = x_586;
goto block_585;
}
block_585:
{
lean_object* x_582; 
if (x_581 == 0)
{
x_582 = x_580;
goto block_583;
}
else
{
lean_object* x_584; 
x_584 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_584, 0, x_579);
x_582 = x_584;
goto block_583;
}
block_583:
{
return x_582;
}
}
}
}
}
else
{
lean_object* x_587; lean_object* x_588; uint8_t x_589; uint8_t x_594; 
lean_del_object(x_535);
lean_dec(x_533);
lean_del_object(x_530);
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_587 = lean_ctor_get(x_537, 0);
x_594 = !lean_is_exclusive(x_537);
if (x_594 == 0)
{
x_588 = x_537;
x_589 = x_594;
goto block_593;
}
else
{
lean_inc(x_587);
lean_dec(x_537);
x_588 = lean_box(0);
x_589 = x_594;
goto block_593;
}
block_593:
{
lean_object* x_590; 
if (x_589 == 0)
{
x_590 = x_588;
goto block_591;
}
else
{
lean_object* x_592; 
x_592 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_592, 0, x_587);
x_590 = x_592;
goto block_591;
}
block_591:
{
return x_590;
}
}
}
}
}
}
else
{
lean_dec(x_528);
x_435 = x_481;
x_436 = x_482;
x_437 = x_483;
x_438 = x_484;
goto block_480;
}
}
else
{
lean_object* x_599; lean_object* x_600; uint8_t x_601; uint8_t x_606; 
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_599 = lean_ctor_get(x_527, 0);
x_606 = !lean_is_exclusive(x_527);
if (x_606 == 0)
{
x_600 = x_527;
x_601 = x_606;
goto block_605;
}
else
{
lean_inc(x_599);
lean_dec(x_527);
x_600 = lean_box(0);
x_601 = x_606;
goto block_605;
}
block_605:
{
lean_object* x_602; 
if (x_601 == 0)
{
x_602 = x_600;
goto block_603;
}
else
{
lean_object* x_604; 
x_604 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_604, 0, x_599);
x_602 = x_604;
goto block_603;
}
block_603:
{
return x_602;
}
}
}
}
}
else
{
lean_object* x_607; lean_object* x_608; uint8_t x_609; uint8_t x_614; 
lean_dec(x_484);
lean_dec_ref(x_483);
lean_dec(x_482);
lean_dec_ref(x_481);
lean_dec_ref(x_148);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_607 = lean_ctor_get(x_485, 0);
x_614 = !lean_is_exclusive(x_485);
if (x_614 == 0)
{
x_608 = x_485;
x_609 = x_614;
goto block_613;
}
else
{
lean_inc(x_607);
lean_dec(x_485);
x_608 = lean_box(0);
x_609 = x_614;
goto block_613;
}
block_613:
{
lean_object* x_610; 
if (x_609 == 0)
{
x_610 = x_608;
goto block_611;
}
else
{
lean_object* x_612; 
x_612 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_612, 0, x_607);
x_610 = x_612;
goto block_611;
}
block_611:
{
return x_610;
}
}
}
}
}
else
{
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_76;
goto block_30;
}
block_75:
{
lean_object* x_40; 
lean_inc(x_2);
x_40 = l_Lean_MVarId_getType(x_2, x_38, x_39, x_36, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_39);
x_43 = l_Lean_Meta_mkNoConfusion(x_41, x_42, x_38, x_39, x_36, x_37);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_44, x_39);
lean_dec(x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_45);
x_46 = lean_box(x_12);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_46);
x_47 = x_33;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_46);
x_47 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
x_17 = x_48;
goto block_23;
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_del_object(x_33);
lean_del_object(x_15);
lean_dec(x_14);
x_51 = lean_ctor_get(x_45, 0);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
x_52 = x_45;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_45);
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
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec(x_39);
lean_del_object(x_33);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_59 = lean_ctor_get(x_43, 0);
x_66 = !lean_is_exclusive(x_43);
if (x_66 == 0)
{
x_60 = x_43;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_43);
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
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_67 = lean_ctor_get(x_40, 0);
x_74 = !lean_is_exclusive(x_40);
if (x_74 == 0)
{
x_68 = x_40;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_40);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
block_97:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_1, 0);
x_82 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
lean_inc(x_81);
lean_inc(x_2);
x_83 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_2, x_82, x_81, x_79, x_80, x_77, x_78);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_76;
goto block_30;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_86 = lean_box(x_12);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_35);
x_17 = x_88;
goto block_23;
}
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_96; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_83, 0);
x_96 = !lean_is_exclusive(x_83);
if (x_96 == 0)
{
x_90 = x_83;
x_91 = x_96;
goto block_95;
}
else
{
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_box(0);
x_91 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_92; 
if (x_91 == 0)
{
x_92 = x_90;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_89);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
}
}
block_103:
{
if (x_102 == 0)
{
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_76;
goto block_30;
}
else
{
x_77 = x_98;
x_78 = x_99;
x_79 = x_100;
x_80 = x_101;
goto block_97;
}
}
block_110:
{
if (x_106 == 0)
{
x_77 = x_105;
x_78 = x_107;
x_79 = x_108;
x_80 = x_109;
goto block_97;
}
else
{
x_98 = x_105;
x_99 = x_107;
x_100 = x_108;
x_101 = x_109;
x_102 = x_104;
goto block_103;
}
}
block_117:
{
if (x_116 == 0)
{
x_98 = x_111;
x_99 = x_113;
x_100 = x_114;
x_101 = x_115;
x_102 = x_104;
goto block_103;
}
else
{
x_105 = x_111;
x_106 = x_112;
x_107 = x_113;
x_108 = x_114;
x_109 = x_115;
goto block_110;
}
}
block_125:
{
uint8_t x_124; 
x_124 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_124 == 0)
{
x_111 = x_122;
x_112 = x_118;
x_113 = x_123;
x_114 = x_120;
x_115 = x_121;
x_116 = x_104;
goto block_117;
}
else
{
if (x_119 == 0)
{
x_105 = x_122;
x_106 = x_118;
x_107 = x_123;
x_108 = x_120;
x_109 = x_121;
goto block_110;
}
else
{
x_111 = x_122;
x_112 = x_118;
x_113 = x_123;
x_114 = x_120;
x_115 = x_121;
x_116 = x_104;
goto block_117;
}
}
}
block_147:
{
if (x_132 == 0)
{
x_118 = x_128;
x_119 = x_129;
x_120 = x_127;
x_121 = x_126;
x_122 = x_130;
x_123 = x_131;
goto block_125;
}
else
{
lean_object* x_133; 
lean_inc(x_131);
lean_inc_ref(x_130);
lean_inc(x_126);
lean_inc_ref(x_127);
lean_inc(x_32);
lean_inc(x_2);
x_133 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_2, x_32, x_127, x_126, x_130, x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
x_118 = x_128;
x_119 = x_129;
x_120 = x_127;
x_121 = x_126;
x_122 = x_130;
x_123 = x_131;
goto block_125;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_136 = lean_box(x_12);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_35);
x_17 = x_138;
goto block_23;
}
}
else
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_146; 
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_139 = lean_ctor_get(x_133, 0);
x_146 = !lean_is_exclusive(x_133);
if (x_146 == 0)
{
x_140 = x_133;
x_141 = x_146;
goto block_145;
}
else
{
lean_inc(x_139);
lean_dec(x_133);
x_140 = lean_box(0);
x_141 = x_146;
goto block_145;
}
block_145:
{
lean_object* x_142; 
if (x_141 == 0)
{
x_142 = x_140;
goto block_143;
}
else
{
lean_object* x_144; 
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_139);
x_142 = x_144;
goto block_143;
}
block_143:
{
return x_142;
}
}
}
}
}
}
}
block_23:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_14);
x_19 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
block_30:
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_5, x_27);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(x_1, x_2, x_3, x_4, x_28, x_26, x_7, x_8, x_9, x_10);
return x_29;
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_702; 
x_14 = lean_ctor_get(x_6, 1);
x_702 = !lean_is_exclusive(x_6);
if (x_702 == 0)
{
lean_object* x_703; 
x_703 = lean_ctor_get(x_6, 0);
lean_dec(x_703);
x_15 = x_6;
x_16 = x_702;
goto block_701;
}
else
{
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_702;
goto block_701;
}
block_701:
{
lean_object* x_17; lean_object* x_24; lean_object* x_25; lean_object* x_31; 
x_24 = lean_box(0);
x_31 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_del_object(x_15);
x_25 = x_14;
goto block_30;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_700; 
x_32 = lean_ctor_get(x_31, 0);
x_700 = !lean_is_exclusive(x_31);
if (x_700 == 0)
{
x_33 = x_31;
x_34 = x_700;
goto block_699;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_700;
goto block_699;
}
block_699:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; uint8_t x_134; 
x_35 = lean_box(0);
x_77 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
x_106 = l_Lean_LocalDecl_isImplementationDetail(x_32);
if (x_106 == 0)
{
lean_object* x_151; uint8_t x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; uint8_t x_168; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; lean_object* x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; uint8_t x_285; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; uint8_t x_294; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; uint8_t x_303; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; uint8_t x_322; uint8_t x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; uint8_t x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_629; 
x_151 = l_Lean_LocalDecl_type(x_32);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_151);
x_629 = l_Lean_Meta_matchNot_x3f(x_151, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
lean_dec_ref(x_629);
if (lean_obj_tag(x_630) == 1)
{
lean_object* x_631; lean_object* x_632; uint8_t x_633; uint8_t x_690; 
x_631 = lean_ctor_get(x_630, 0);
x_690 = !lean_is_exclusive(x_630);
if (x_690 == 0)
{
x_632 = x_630;
x_633 = x_690;
goto block_689;
}
else
{
lean_inc(x_631);
lean_dec(x_630);
x_632 = lean_box(0);
x_633 = x_690;
goto block_689;
}
block_689:
{
lean_object* x_634; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_634 = l_Lean_Meta_findLocalDeclWithType_x3f(x_631, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
lean_dec_ref(x_634);
if (lean_obj_tag(x_635) == 1)
{
lean_object* x_636; lean_object* x_637; uint8_t x_638; uint8_t x_680; 
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec_ref(x_1);
x_636 = lean_ctor_get(x_635, 0);
x_680 = !lean_is_exclusive(x_635);
if (x_680 == 0)
{
x_637 = x_635;
x_638 = x_680;
goto block_679;
}
else
{
lean_inc(x_636);
lean_dec(x_635);
x_637 = lean_box(0);
x_638 = x_680;
goto block_679;
}
block_679:
{
lean_object* x_639; 
lean_inc(x_2);
x_639 = l_Lean_MVarId_getType(x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
lean_dec_ref(x_639);
x_641 = l_Lean_LocalDecl_toExpr(x_32);
x_642 = l_Lean_mkFVar(x_636);
x_643 = l_Lean_Expr_app___override(x_641, x_642);
lean_inc(x_8);
x_644 = l_Lean_Meta_mkFalseElim(x_640, x_643, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; 
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
lean_dec_ref(x_644);
x_646 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_645, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; 
lean_dec_ref(x_646);
x_647 = lean_box(x_12);
if (x_638 == 0)
{
lean_ctor_set(x_637, 0, x_647);
x_648 = x_637;
goto block_653;
}
else
{
lean_object* x_654; 
x_654 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_654, 0, x_647);
x_648 = x_654;
goto block_653;
}
block_653:
{
lean_object* x_649; lean_object* x_650; 
x_649 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_649, 0, x_648);
lean_ctor_set(x_649, 1, x_35);
if (x_633 == 0)
{
lean_ctor_set_tag(x_632, 0);
lean_ctor_set(x_632, 0, x_649);
x_650 = x_632;
goto block_651;
}
else
{
lean_object* x_652; 
x_652 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_652, 0, x_649);
x_650 = x_652;
goto block_651;
}
block_651:
{
x_17 = x_650;
goto block_23;
}
}
}
else
{
lean_object* x_655; lean_object* x_656; uint8_t x_657; uint8_t x_662; 
lean_del_object(x_637);
lean_del_object(x_632);
lean_del_object(x_15);
lean_dec(x_14);
x_655 = lean_ctor_get(x_646, 0);
x_662 = !lean_is_exclusive(x_646);
if (x_662 == 0)
{
x_656 = x_646;
x_657 = x_662;
goto block_661;
}
else
{
lean_inc(x_655);
lean_dec(x_646);
x_656 = lean_box(0);
x_657 = x_662;
goto block_661;
}
block_661:
{
lean_object* x_658; 
if (x_657 == 0)
{
x_658 = x_656;
goto block_659;
}
else
{
lean_object* x_660; 
x_660 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_660, 0, x_655);
x_658 = x_660;
goto block_659;
}
block_659:
{
return x_658;
}
}
}
}
else
{
lean_object* x_663; lean_object* x_664; uint8_t x_665; uint8_t x_670; 
lean_del_object(x_637);
lean_del_object(x_632);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
x_663 = lean_ctor_get(x_644, 0);
x_670 = !lean_is_exclusive(x_644);
if (x_670 == 0)
{
x_664 = x_644;
x_665 = x_670;
goto block_669;
}
else
{
lean_inc(x_663);
lean_dec(x_644);
x_664 = lean_box(0);
x_665 = x_670;
goto block_669;
}
block_669:
{
lean_object* x_666; 
if (x_665 == 0)
{
x_666 = x_664;
goto block_667;
}
else
{
lean_object* x_668; 
x_668 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_668, 0, x_663);
x_666 = x_668;
goto block_667;
}
block_667:
{
return x_666;
}
}
}
}
else
{
lean_object* x_671; lean_object* x_672; uint8_t x_673; uint8_t x_678; 
lean_del_object(x_637);
lean_dec(x_636);
lean_del_object(x_632);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_671 = lean_ctor_get(x_639, 0);
x_678 = !lean_is_exclusive(x_639);
if (x_678 == 0)
{
x_672 = x_639;
x_673 = x_678;
goto block_677;
}
else
{
lean_inc(x_671);
lean_dec(x_639);
x_672 = lean_box(0);
x_673 = x_678;
goto block_677;
}
block_677:
{
lean_object* x_674; 
if (x_673 == 0)
{
x_674 = x_672;
goto block_675;
}
else
{
lean_object* x_676; 
x_676 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_676, 0, x_671);
x_674 = x_676;
goto block_675;
}
block_675:
{
return x_674;
}
}
}
}
}
else
{
lean_dec(x_635);
lean_del_object(x_632);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_492 = x_7;
x_493 = x_8;
x_494 = x_9;
x_495 = x_10;
goto block_628;
}
}
else
{
lean_object* x_681; lean_object* x_682; uint8_t x_683; uint8_t x_688; 
lean_del_object(x_632);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_681 = lean_ctor_get(x_634, 0);
x_688 = !lean_is_exclusive(x_634);
if (x_688 == 0)
{
x_682 = x_634;
x_683 = x_688;
goto block_687;
}
else
{
lean_inc(x_681);
lean_dec(x_634);
x_682 = lean_box(0);
x_683 = x_688;
goto block_687;
}
block_687:
{
lean_object* x_684; 
if (x_683 == 0)
{
x_684 = x_682;
goto block_685;
}
else
{
lean_object* x_686; 
x_686 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_686, 0, x_681);
x_684 = x_686;
goto block_685;
}
block_685:
{
return x_684;
}
}
}
}
}
else
{
lean_dec(x_630);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_492 = x_7;
x_493 = x_8;
x_494 = x_9;
x_495 = x_10;
goto block_628;
}
}
else
{
lean_object* x_691; lean_object* x_692; uint8_t x_693; uint8_t x_698; 
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_691 = lean_ctor_get(x_629, 0);
x_698 = !lean_is_exclusive(x_629);
if (x_698 == 0)
{
x_692 = x_629;
x_693 = x_698;
goto block_697;
}
else
{
lean_inc(x_691);
lean_dec(x_629);
x_692 = lean_box(0);
x_693 = x_698;
goto block_697;
}
block_697:
{
lean_object* x_694; 
if (x_693 == 0)
{
x_694 = x_692;
goto block_695;
}
else
{
lean_object* x_696; 
x_696 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_696, 0, x_691);
x_694 = x_696;
goto block_695;
}
block_695:
{
return x_694;
}
}
}
block_160:
{
uint8_t x_158; 
x_158 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_158 == 0)
{
lean_dec_ref(x_151);
x_128 = x_152;
x_129 = x_157;
x_130 = x_156;
x_131 = x_154;
x_132 = x_155;
x_133 = x_153;
x_134 = x_106;
goto block_150;
}
else
{
uint8_t x_159; 
x_159 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_151);
x_128 = x_152;
x_129 = x_157;
x_130 = x_156;
x_131 = x_154;
x_132 = x_155;
x_133 = x_153;
x_134 = x_159;
goto block_150;
}
}
block_170:
{
if (x_168 == 0)
{
lean_dec_ref(x_163);
x_152 = x_164;
x_153 = x_166;
x_154 = x_165;
x_155 = x_161;
x_156 = x_167;
x_157 = x_162;
goto block_160;
}
else
{
lean_object* x_169; 
lean_dec_ref(x_167);
lean_dec_ref(x_165);
lean_dec(x_162);
lean_dec(x_161);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_163);
return x_169;
}
}
block_180:
{
uint8_t x_178; 
x_178 = l_Lean_Exception_isInterrupt(x_177);
if (x_178 == 0)
{
uint8_t x_179; 
lean_inc_ref(x_177);
x_179 = l_Lean_Exception_isRuntime(x_177);
x_161 = x_171;
x_162 = x_172;
x_163 = x_177;
x_164 = x_173;
x_165 = x_174;
x_166 = x_176;
x_167 = x_175;
x_168 = x_179;
goto block_170;
}
else
{
x_161 = x_171;
x_162 = x_172;
x_163 = x_177;
x_164 = x_173;
x_165 = x_174;
x_166 = x_176;
x_167 = x_175;
x_168 = x_178;
goto block_170;
}
}
block_278:
{
lean_object* x_187; 
lean_inc(x_182);
lean_inc_ref(x_186);
lean_inc(x_181);
lean_inc_ref(x_184);
lean_inc_ref(x_151);
x_187 = l_Lean_Meta_mkDecide(x_151, x_184, x_181, x_186, x_182);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; uint8_t x_276; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_189 = l_Lean_Meta_Context_config(x_184);
x_190 = lean_ctor_get_uint8(x_189, 0);
x_191 = lean_ctor_get_uint8(x_189, 1);
x_192 = lean_ctor_get_uint8(x_189, 2);
x_193 = lean_ctor_get_uint8(x_189, 3);
x_194 = lean_ctor_get_uint8(x_189, 4);
x_195 = lean_ctor_get_uint8(x_189, 5);
x_196 = lean_ctor_get_uint8(x_189, 6);
x_197 = lean_ctor_get_uint8(x_189, 7);
x_198 = lean_ctor_get_uint8(x_189, 8);
x_199 = lean_ctor_get_uint8(x_189, 10);
x_200 = lean_ctor_get_uint8(x_189, 11);
x_201 = lean_ctor_get_uint8(x_189, 12);
x_202 = lean_ctor_get_uint8(x_189, 13);
x_203 = lean_ctor_get_uint8(x_189, 14);
x_204 = lean_ctor_get_uint8(x_189, 15);
x_205 = lean_ctor_get_uint8(x_189, 16);
x_206 = lean_ctor_get_uint8(x_189, 17);
x_207 = lean_ctor_get_uint8(x_189, 18);
x_276 = !lean_is_exclusive(x_189);
if (x_276 == 0)
{
x_208 = x_189;
x_209 = x_276;
goto block_275;
}
else
{
lean_dec(x_189);
x_208 = lean_box(0);
x_209 = x_276;
goto block_275;
}
block_275:
{
uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; lean_object* x_221; 
x_210 = lean_ctor_get_uint8(x_184, sizeof(void*)*7);
x_211 = lean_ctor_get(x_184, 1);
x_212 = lean_ctor_get(x_184, 2);
x_213 = lean_ctor_get(x_184, 3);
x_214 = lean_ctor_get(x_184, 4);
x_215 = lean_ctor_get(x_184, 5);
x_216 = lean_ctor_get(x_184, 6);
x_217 = lean_ctor_get_uint8(x_184, sizeof(void*)*7 + 1);
x_218 = lean_ctor_get_uint8(x_184, sizeof(void*)*7 + 2);
x_219 = lean_ctor_get_uint8(x_184, sizeof(void*)*7 + 3);
x_220 = 1;
if (x_209 == 0)
{
x_221 = x_208;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_274, 0, x_190);
lean_ctor_set_uint8(x_274, 1, x_191);
lean_ctor_set_uint8(x_274, 2, x_192);
lean_ctor_set_uint8(x_274, 3, x_193);
lean_ctor_set_uint8(x_274, 4, x_194);
lean_ctor_set_uint8(x_274, 5, x_195);
lean_ctor_set_uint8(x_274, 6, x_196);
lean_ctor_set_uint8(x_274, 7, x_197);
lean_ctor_set_uint8(x_274, 8, x_198);
lean_ctor_set_uint8(x_274, 10, x_199);
lean_ctor_set_uint8(x_274, 11, x_200);
lean_ctor_set_uint8(x_274, 12, x_201);
lean_ctor_set_uint8(x_274, 13, x_202);
lean_ctor_set_uint8(x_274, 14, x_203);
lean_ctor_set_uint8(x_274, 15, x_204);
lean_ctor_set_uint8(x_274, 16, x_205);
lean_ctor_set_uint8(x_274, 17, x_206);
lean_ctor_set_uint8(x_274, 18, x_207);
x_221 = x_274;
goto block_273;
}
block_273:
{
uint64_t x_222; uint64_t x_223; uint64_t x_224; uint64_t x_225; uint64_t x_226; uint64_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_ctor_set_uint8(x_221, 9, x_220);
x_222 = l_Lean_Meta_Context_configKey(x_184);
x_223 = 2;
x_224 = lean_uint64_shift_right(x_222, x_223);
x_225 = lean_uint64_shift_left(x_224, x_223);
x_226 = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
x_227 = lean_uint64_lor(x_225, x_226);
x_228 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set_uint64(x_228, sizeof(void*)*1, x_227);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc_ref(x_213);
lean_inc_ref(x_212);
lean_inc(x_211);
x_229 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_211);
lean_ctor_set(x_229, 2, x_212);
lean_ctor_set(x_229, 3, x_213);
lean_ctor_set(x_229, 4, x_214);
lean_ctor_set(x_229, 5, x_215);
lean_ctor_set(x_229, 6, x_216);
lean_ctor_set_uint8(x_229, sizeof(void*)*7, x_210);
lean_ctor_set_uint8(x_229, sizeof(void*)*7 + 1, x_217);
lean_ctor_set_uint8(x_229, sizeof(void*)*7 + 2, x_218);
lean_ctor_set_uint8(x_229, sizeof(void*)*7 + 3, x_219);
lean_inc(x_182);
lean_inc_ref(x_186);
lean_inc(x_181);
lean_inc(x_188);
x_230 = lean_whnf(x_188, x_229, x_181, x_186, x_182);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
lean_dec_ref(x_230);
x_232 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
x_233 = l_Lean_Expr_isConstOf(x_231, x_232);
lean_dec(x_231);
if (x_233 == 0)
{
lean_dec(x_188);
x_152 = x_183;
x_153 = x_185;
x_154 = x_184;
x_155 = x_181;
x_156 = x_186;
x_157 = x_182;
goto block_160;
}
else
{
lean_object* x_234; 
lean_inc(x_182);
lean_inc_ref(x_186);
lean_inc(x_181);
lean_inc_ref(x_184);
lean_inc(x_188);
x_234 = l_Lean_Meta_mkEqRefl(x_188, x_184, x_181, x_186, x_182);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec_ref(x_234);
lean_inc(x_2);
x_236 = l_Lean_MVarId_getType(x_2, x_184, x_181, x_186, x_182);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec_ref(x_236);
x_238 = l_Lean_Expr_getAppNumArgs(x_188);
x_239 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
x_240 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(x_238);
x_241 = lean_mk_array(x_238, x_240);
x_242 = lean_unsigned_to_nat(1u);
x_243 = lean_nat_sub(x_238, x_242);
lean_dec(x_238);
x_244 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_188, x_241, x_243);
x_245 = lean_array_push(x_244, x_235);
x_246 = l_Lean_mkAppN(x_239, x_245);
lean_dec_ref(x_245);
lean_inc(x_32);
x_247 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_182);
lean_inc_ref(x_186);
lean_inc(x_181);
lean_inc_ref(x_184);
x_248 = l_Lean_Meta_mkAbsurd(x_237, x_247, x_246, x_184, x_181, x_186, x_182);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_268; 
x_249 = lean_ctor_get(x_248, 0);
x_268 = !lean_is_exclusive(x_248);
if (x_268 == 0)
{
x_250 = x_248;
x_251 = x_268;
goto block_267;
}
else
{
lean_inc(x_249);
lean_dec(x_248);
x_250 = lean_box(0);
x_251 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_252; 
lean_inc(x_2);
x_252 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_249, x_181);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; uint8_t x_254; uint8_t x_264; 
lean_dec_ref(x_186);
lean_dec_ref(x_184);
lean_dec(x_182);
lean_dec(x_181);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_264 = !lean_is_exclusive(x_252);
if (x_264 == 0)
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_252, 0);
lean_dec(x_265);
x_253 = x_252;
x_254 = x_264;
goto block_263;
}
else
{
lean_dec(x_252);
x_253 = lean_box(0);
x_254 = x_264;
goto block_263;
}
block_263:
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_box(x_12);
if (x_254 == 0)
{
lean_ctor_set_tag(x_253, 1);
lean_ctor_set(x_253, 0, x_255);
x_256 = x_253;
goto block_261;
}
else
{
lean_object* x_262; 
x_262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_262, 0, x_255);
x_256 = x_262;
goto block_261;
}
block_261:
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_35);
if (x_251 == 0)
{
lean_ctor_set(x_250, 0, x_257);
x_258 = x_250;
goto block_259;
}
else
{
lean_object* x_260; 
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_257);
x_258 = x_260;
goto block_259;
}
block_259:
{
x_17 = x_258;
goto block_23;
}
}
}
}
else
{
lean_object* x_266; 
lean_del_object(x_250);
x_266 = lean_ctor_get(x_252, 0);
lean_inc(x_266);
lean_dec_ref(x_252);
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_184;
x_175 = x_186;
x_176 = x_185;
x_177 = x_266;
goto block_180;
}
}
}
else
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_248, 0);
lean_inc(x_269);
lean_dec_ref(x_248);
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_184;
x_175 = x_186;
x_176 = x_185;
x_177 = x_269;
goto block_180;
}
}
else
{
lean_object* x_270; 
lean_dec(x_235);
lean_dec(x_188);
x_270 = lean_ctor_get(x_236, 0);
lean_inc(x_270);
lean_dec_ref(x_236);
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_184;
x_175 = x_186;
x_176 = x_185;
x_177 = x_270;
goto block_180;
}
}
else
{
lean_object* x_271; 
lean_dec(x_188);
x_271 = lean_ctor_get(x_234, 0);
lean_inc(x_271);
lean_dec_ref(x_234);
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_184;
x_175 = x_186;
x_176 = x_185;
x_177 = x_271;
goto block_180;
}
}
}
else
{
lean_object* x_272; 
lean_dec(x_188);
x_272 = lean_ctor_get(x_230, 0);
lean_inc(x_272);
lean_dec_ref(x_230);
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_184;
x_175 = x_186;
x_176 = x_185;
x_177 = x_272;
goto block_180;
}
}
}
}
else
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_187, 0);
lean_inc(x_277);
lean_dec_ref(x_187);
x_171 = x_181;
x_172 = x_182;
x_173 = x_183;
x_174 = x_184;
x_175 = x_186;
x_176 = x_185;
x_177 = x_277;
goto block_180;
}
}
block_286:
{
if (x_285 == 0)
{
x_152 = x_281;
x_153 = x_283;
x_154 = x_282;
x_155 = x_279;
x_156 = x_284;
x_157 = x_280;
goto block_160;
}
else
{
x_181 = x_279;
x_182 = x_280;
x_183 = x_281;
x_184 = x_282;
x_185 = x_283;
x_186 = x_284;
goto block_278;
}
}
block_296:
{
if (x_294 == 0)
{
lean_dec_ref(x_291);
x_279 = x_287;
x_280 = x_288;
x_281 = x_289;
x_282 = x_290;
x_283 = x_293;
x_284 = x_292;
x_285 = x_106;
goto block_286;
}
else
{
uint8_t x_295; 
x_295 = l_Lean_Expr_hasFVar(x_291);
lean_dec_ref(x_291);
if (x_295 == 0)
{
x_181 = x_287;
x_182 = x_288;
x_183 = x_289;
x_184 = x_290;
x_185 = x_293;
x_186 = x_292;
goto block_278;
}
else
{
x_279 = x_287;
x_280 = x_288;
x_281 = x_289;
x_282 = x_290;
x_283 = x_293;
x_284 = x_292;
x_285 = x_106;
goto block_286;
}
}
}
block_315:
{
lean_object* x_304; 
lean_inc_ref(x_151);
x_304 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_151, x_297);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; uint8_t x_306; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
lean_dec_ref(x_304);
x_306 = l_Lean_Expr_hasMVar(x_305);
if (x_306 == 0)
{
x_287 = x_297;
x_288 = x_298;
x_289 = x_299;
x_290 = x_300;
x_291 = x_305;
x_292 = x_301;
x_293 = x_302;
x_294 = x_303;
goto block_296;
}
else
{
x_287 = x_297;
x_288 = x_298;
x_289 = x_299;
x_290 = x_300;
x_291 = x_305;
x_292 = x_301;
x_293 = x_302;
x_294 = x_106;
goto block_296;
}
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; uint8_t x_314; 
lean_dec_ref(x_301);
lean_dec_ref(x_300);
lean_dec(x_298);
lean_dec(x_297);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_307 = lean_ctor_get(x_304, 0);
x_314 = !lean_is_exclusive(x_304);
if (x_314 == 0)
{
x_308 = x_304;
x_309 = x_314;
goto block_313;
}
else
{
lean_inc(x_307);
lean_dec(x_304);
x_308 = lean_box(0);
x_309 = x_314;
goto block_313;
}
block_313:
{
lean_object* x_310; 
if (x_309 == 0)
{
x_310 = x_308;
goto block_311;
}
else
{
lean_object* x_312; 
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_307);
x_310 = x_312;
goto block_311;
}
block_311:
{
return x_310;
}
}
}
}
block_323:
{
if (x_322 == 0)
{
x_152 = x_318;
x_153 = x_320;
x_154 = x_319;
x_155 = x_316;
x_156 = x_321;
x_157 = x_317;
goto block_160;
}
else
{
x_297 = x_316;
x_298 = x_317;
x_299 = x_318;
x_300 = x_319;
x_301 = x_321;
x_302 = x_320;
x_303 = x_322;
goto block_315;
}
}
block_332:
{
uint8_t x_330; 
x_330 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_330 == 0)
{
x_316 = x_327;
x_317 = x_329;
x_318 = x_325;
x_319 = x_326;
x_320 = x_324;
x_321 = x_328;
x_322 = x_106;
goto block_323;
}
else
{
uint8_t x_331; 
x_331 = l_Lean_Expr_hasFVar(x_151);
if (x_331 == 0)
{
x_297 = x_327;
x_298 = x_329;
x_299 = x_325;
x_300 = x_326;
x_301 = x_328;
x_302 = x_324;
x_303 = x_330;
goto block_315;
}
else
{
x_316 = x_327;
x_317 = x_329;
x_318 = x_325;
x_319 = x_326;
x_320 = x_324;
x_321 = x_328;
x_322 = x_106;
goto block_323;
}
}
}
block_395:
{
lean_object* x_340; 
lean_inc(x_338);
lean_inc_ref(x_333);
lean_inc(x_336);
lean_inc_ref(x_335);
x_340 = l_Lean_Meta_isExprDefEq(x_339, x_334, x_335, x_336, x_333, x_338);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; uint8_t x_342; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
lean_dec_ref(x_340);
x_342 = lean_unbox(x_341);
lean_dec(x_341);
if (x_342 == 0)
{
x_324 = x_337;
x_325 = x_12;
x_326 = x_335;
x_327 = x_336;
x_328 = x_333;
x_329 = x_338;
goto block_332;
}
else
{
lean_object* x_343; 
lean_dec_ref(x_151);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_343 = l_Lean_MVarId_getType(x_2, x_335, x_336, x_333, x_338);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec_ref(x_343);
x_345 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_338);
lean_inc_ref(x_333);
lean_inc(x_336);
lean_inc_ref(x_335);
x_346 = l_Lean_Meta_mkEqOfHEq(x_345, x_12, x_335, x_336, x_333, x_338);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
lean_dec_ref(x_346);
lean_inc(x_336);
x_348 = l_Lean_Meta_mkNoConfusion(x_344, x_347, x_335, x_336, x_333, x_338);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
lean_dec_ref(x_348);
x_350 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_349, x_336);
lean_dec(x_336);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec_ref(x_350);
x_351 = lean_box(x_12);
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_351);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_35);
x_354 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_354, 0, x_353);
x_17 = x_354;
goto block_23;
}
else
{
lean_object* x_355; lean_object* x_356; uint8_t x_357; uint8_t x_362; 
lean_del_object(x_15);
lean_dec(x_14);
x_355 = lean_ctor_get(x_350, 0);
x_362 = !lean_is_exclusive(x_350);
if (x_362 == 0)
{
x_356 = x_350;
x_357 = x_362;
goto block_361;
}
else
{
lean_inc(x_355);
lean_dec(x_350);
x_356 = lean_box(0);
x_357 = x_362;
goto block_361;
}
block_361:
{
lean_object* x_358; 
if (x_357 == 0)
{
x_358 = x_356;
goto block_359;
}
else
{
lean_object* x_360; 
x_360 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_360, 0, x_355);
x_358 = x_360;
goto block_359;
}
block_359:
{
return x_358;
}
}
}
}
else
{
lean_object* x_363; lean_object* x_364; uint8_t x_365; uint8_t x_370; 
lean_dec(x_336);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_363 = lean_ctor_get(x_348, 0);
x_370 = !lean_is_exclusive(x_348);
if (x_370 == 0)
{
x_364 = x_348;
x_365 = x_370;
goto block_369;
}
else
{
lean_inc(x_363);
lean_dec(x_348);
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
lean_dec(x_344);
lean_dec(x_338);
lean_dec(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_333);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_371 = lean_ctor_get(x_346, 0);
x_378 = !lean_is_exclusive(x_346);
if (x_378 == 0)
{
x_372 = x_346;
x_373 = x_378;
goto block_377;
}
else
{
lean_inc(x_371);
lean_dec(x_346);
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
lean_dec(x_338);
lean_dec(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_333);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_379 = lean_ctor_get(x_343, 0);
x_386 = !lean_is_exclusive(x_343);
if (x_386 == 0)
{
x_380 = x_343;
x_381 = x_386;
goto block_385;
}
else
{
lean_inc(x_379);
lean_dec(x_343);
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
}
else
{
lean_object* x_387; lean_object* x_388; uint8_t x_389; uint8_t x_394; 
lean_dec(x_338);
lean_dec(x_336);
lean_dec_ref(x_335);
lean_dec_ref(x_333);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_387 = lean_ctor_get(x_340, 0);
x_394 = !lean_is_exclusive(x_340);
if (x_394 == 0)
{
x_388 = x_340;
x_389 = x_394;
goto block_393;
}
else
{
lean_inc(x_387);
lean_dec(x_340);
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
block_445:
{
lean_object* x_401; 
lean_inc(x_400);
lean_inc_ref(x_399);
lean_inc(x_398);
lean_inc_ref(x_397);
lean_inc_ref(x_151);
x_401 = l_Lean_Meta_matchHEq_x3f(x_151, x_397, x_398, x_399, x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
lean_dec_ref(x_401);
if (lean_obj_tag(x_402) == 1)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
lean_dec_ref(x_402);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_403, 0);
lean_inc(x_406);
lean_dec(x_403);
x_407 = lean_ctor_get(x_404, 0);
lean_inc(x_407);
lean_dec(x_404);
x_408 = lean_ctor_get(x_405, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_405, 1);
lean_inc(x_409);
lean_dec(x_405);
lean_inc(x_400);
lean_inc_ref(x_399);
lean_inc(x_398);
lean_inc_ref(x_397);
x_410 = l_Lean_Meta_matchConstructorApp_x3f(x_407, x_397, x_398, x_399, x_400);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
lean_dec_ref(x_410);
if (lean_obj_tag(x_411) == 1)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
lean_dec_ref(x_411);
lean_inc(x_400);
lean_inc_ref(x_399);
lean_inc(x_398);
lean_inc_ref(x_397);
x_413 = l_Lean_Meta_matchConstructorApp_x3f(x_409, x_397, x_398, x_399, x_400);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
lean_dec_ref(x_413);
if (lean_obj_tag(x_414) == 1)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_415 = lean_ctor_get(x_412, 0);
lean_inc_ref(x_415);
lean_dec(x_412);
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
lean_dec_ref(x_414);
x_417 = lean_ctor_get(x_416, 0);
lean_inc_ref(x_417);
lean_dec(x_416);
x_418 = lean_ctor_get(x_415, 0);
lean_inc(x_418);
lean_dec_ref(x_415);
x_419 = lean_ctor_get(x_417, 0);
lean_inc(x_419);
lean_dec_ref(x_417);
x_420 = lean_name_eq(x_418, x_419);
lean_dec(x_419);
lean_dec(x_418);
if (x_420 == 0)
{
x_333 = x_399;
x_334 = x_408;
x_335 = x_397;
x_336 = x_398;
x_337 = x_396;
x_338 = x_400;
x_339 = x_406;
goto block_395;
}
else
{
if (x_106 == 0)
{
lean_dec(x_408);
lean_dec(x_406);
x_324 = x_396;
x_325 = x_12;
x_326 = x_397;
x_327 = x_398;
x_328 = x_399;
x_329 = x_400;
goto block_332;
}
else
{
x_333 = x_399;
x_334 = x_408;
x_335 = x_397;
x_336 = x_398;
x_337 = x_396;
x_338 = x_400;
x_339 = x_406;
goto block_395;
}
}
}
else
{
lean_dec(x_414);
lean_dec(x_412);
lean_dec(x_408);
lean_dec(x_406);
x_324 = x_396;
x_325 = x_12;
x_326 = x_397;
x_327 = x_398;
x_328 = x_399;
x_329 = x_400;
goto block_332;
}
}
else
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; uint8_t x_428; 
lean_dec(x_412);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_400);
lean_dec_ref(x_399);
lean_dec(x_398);
lean_dec_ref(x_397);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_421 = lean_ctor_get(x_413, 0);
x_428 = !lean_is_exclusive(x_413);
if (x_428 == 0)
{
x_422 = x_413;
x_423 = x_428;
goto block_427;
}
else
{
lean_inc(x_421);
lean_dec(x_413);
x_422 = lean_box(0);
x_423 = x_428;
goto block_427;
}
block_427:
{
lean_object* x_424; 
if (x_423 == 0)
{
x_424 = x_422;
goto block_425;
}
else
{
lean_object* x_426; 
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_421);
x_424 = x_426;
goto block_425;
}
block_425:
{
return x_424;
}
}
}
}
else
{
lean_dec(x_411);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_406);
x_324 = x_396;
x_325 = x_12;
x_326 = x_397;
x_327 = x_398;
x_328 = x_399;
x_329 = x_400;
goto block_332;
}
}
else
{
lean_object* x_429; lean_object* x_430; uint8_t x_431; uint8_t x_436; 
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_400);
lean_dec_ref(x_399);
lean_dec(x_398);
lean_dec_ref(x_397);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_429 = lean_ctor_get(x_410, 0);
x_436 = !lean_is_exclusive(x_410);
if (x_436 == 0)
{
x_430 = x_410;
x_431 = x_436;
goto block_435;
}
else
{
lean_inc(x_429);
lean_dec(x_410);
x_430 = lean_box(0);
x_431 = x_436;
goto block_435;
}
block_435:
{
lean_object* x_432; 
if (x_431 == 0)
{
x_432 = x_430;
goto block_433;
}
else
{
lean_object* x_434; 
x_434 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_434, 0, x_429);
x_432 = x_434;
goto block_433;
}
block_433:
{
return x_432;
}
}
}
}
else
{
lean_dec(x_402);
x_324 = x_396;
x_325 = x_106;
x_326 = x_397;
x_327 = x_398;
x_328 = x_399;
x_329 = x_400;
goto block_332;
}
}
else
{
lean_object* x_437; lean_object* x_438; uint8_t x_439; uint8_t x_444; 
lean_dec(x_400);
lean_dec_ref(x_399);
lean_dec(x_398);
lean_dec_ref(x_397);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_437 = lean_ctor_get(x_401, 0);
x_444 = !lean_is_exclusive(x_401);
if (x_444 == 0)
{
x_438 = x_401;
x_439 = x_444;
goto block_443;
}
else
{
lean_inc(x_437);
lean_dec(x_401);
x_438 = lean_box(0);
x_439 = x_444;
goto block_443;
}
block_443:
{
lean_object* x_440; 
if (x_439 == 0)
{
x_440 = x_438;
goto block_441;
}
else
{
lean_object* x_442; 
x_442 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_442, 0, x_437);
x_440 = x_442;
goto block_441;
}
block_441:
{
return x_440;
}
}
}
}
block_491:
{
lean_object* x_450; 
lean_inc(x_449);
lean_inc_ref(x_448);
lean_inc(x_447);
lean_inc_ref(x_446);
lean_inc_ref(x_151);
x_450 = l_Lean_Meta_matchEq_x3f(x_151, x_446, x_447, x_448, x_449);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
lean_dec_ref(x_450);
if (lean_obj_tag(x_451) == 1)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
lean_dec_ref(x_451);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
lean_dec(x_452);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
lean_inc(x_449);
lean_inc_ref(x_448);
lean_inc(x_447);
lean_inc_ref(x_446);
x_456 = l_Lean_Meta_matchConstructorApp_x3f(x_454, x_446, x_447, x_448, x_449);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
lean_dec_ref(x_456);
if (lean_obj_tag(x_457) == 1)
{
lean_object* x_458; lean_object* x_459; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
lean_dec_ref(x_457);
lean_inc(x_449);
lean_inc_ref(x_448);
lean_inc(x_447);
lean_inc_ref(x_446);
x_459 = l_Lean_Meta_matchConstructorApp_x3f(x_455, x_446, x_447, x_448, x_449);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
lean_dec_ref(x_459);
if (lean_obj_tag(x_460) == 1)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_461 = lean_ctor_get(x_458, 0);
lean_inc_ref(x_461);
lean_dec(x_458);
x_462 = lean_ctor_get(x_460, 0);
lean_inc(x_462);
lean_dec_ref(x_460);
x_463 = lean_ctor_get(x_462, 0);
lean_inc_ref(x_463);
lean_dec(x_462);
x_464 = lean_ctor_get(x_461, 0);
lean_inc(x_464);
lean_dec_ref(x_461);
x_465 = lean_ctor_get(x_463, 0);
lean_inc(x_465);
lean_dec_ref(x_463);
x_466 = lean_name_eq(x_464, x_465);
lean_dec(x_465);
lean_dec(x_464);
if (x_466 == 0)
{
lean_dec_ref(x_151);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_36 = x_446;
x_37 = x_448;
x_38 = x_447;
x_39 = x_449;
goto block_76;
}
else
{
if (x_106 == 0)
{
lean_del_object(x_33);
x_396 = x_12;
x_397 = x_446;
x_398 = x_447;
x_399 = x_448;
x_400 = x_449;
goto block_445;
}
else
{
lean_dec_ref(x_151);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_36 = x_446;
x_37 = x_448;
x_38 = x_447;
x_39 = x_449;
goto block_76;
}
}
}
else
{
lean_dec(x_460);
lean_dec(x_458);
lean_del_object(x_33);
x_396 = x_12;
x_397 = x_446;
x_398 = x_447;
x_399 = x_448;
x_400 = x_449;
goto block_445;
}
}
else
{
lean_object* x_467; lean_object* x_468; uint8_t x_469; uint8_t x_474; 
lean_dec(x_458);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_467 = lean_ctor_get(x_459, 0);
x_474 = !lean_is_exclusive(x_459);
if (x_474 == 0)
{
x_468 = x_459;
x_469 = x_474;
goto block_473;
}
else
{
lean_inc(x_467);
lean_dec(x_459);
x_468 = lean_box(0);
x_469 = x_474;
goto block_473;
}
block_473:
{
lean_object* x_470; 
if (x_469 == 0)
{
x_470 = x_468;
goto block_471;
}
else
{
lean_object* x_472; 
x_472 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_472, 0, x_467);
x_470 = x_472;
goto block_471;
}
block_471:
{
return x_470;
}
}
}
}
else
{
lean_dec(x_457);
lean_dec(x_455);
lean_del_object(x_33);
x_396 = x_12;
x_397 = x_446;
x_398 = x_447;
x_399 = x_448;
x_400 = x_449;
goto block_445;
}
}
else
{
lean_object* x_475; lean_object* x_476; uint8_t x_477; uint8_t x_482; 
lean_dec(x_455);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_475 = lean_ctor_get(x_456, 0);
x_482 = !lean_is_exclusive(x_456);
if (x_482 == 0)
{
x_476 = x_456;
x_477 = x_482;
goto block_481;
}
else
{
lean_inc(x_475);
lean_dec(x_456);
x_476 = lean_box(0);
x_477 = x_482;
goto block_481;
}
block_481:
{
lean_object* x_478; 
if (x_477 == 0)
{
x_478 = x_476;
goto block_479;
}
else
{
lean_object* x_480; 
x_480 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_480, 0, x_475);
x_478 = x_480;
goto block_479;
}
block_479:
{
return x_478;
}
}
}
}
else
{
lean_dec(x_451);
lean_del_object(x_33);
x_396 = x_106;
x_397 = x_446;
x_398 = x_447;
x_399 = x_448;
x_400 = x_449;
goto block_445;
}
}
else
{
lean_object* x_483; lean_object* x_484; uint8_t x_485; uint8_t x_490; 
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_483 = lean_ctor_get(x_450, 0);
x_490 = !lean_is_exclusive(x_450);
if (x_490 == 0)
{
x_484 = x_450;
x_485 = x_490;
goto block_489;
}
else
{
lean_inc(x_483);
lean_dec(x_450);
x_484 = lean_box(0);
x_485 = x_490;
goto block_489;
}
block_489:
{
lean_object* x_486; 
if (x_485 == 0)
{
x_486 = x_484;
goto block_487;
}
else
{
lean_object* x_488; 
x_488 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_488, 0, x_483);
x_486 = x_488;
goto block_487;
}
block_487:
{
return x_486;
}
}
}
}
block_628:
{
lean_object* x_496; 
lean_inc(x_495);
lean_inc_ref(x_494);
lean_inc(x_493);
lean_inc_ref(x_492);
lean_inc_ref(x_151);
x_496 = l_refutableHasNotBit_x3f(x_151, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
lean_dec_ref(x_496);
if (lean_obj_tag(x_497) == 1)
{
lean_object* x_498; lean_object* x_499; uint8_t x_500; uint8_t x_538; 
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_498 = lean_ctor_get(x_497, 0);
x_538 = !lean_is_exclusive(x_497);
if (x_538 == 0)
{
x_499 = x_497;
x_500 = x_538;
goto block_537;
}
else
{
lean_inc(x_498);
lean_dec(x_497);
x_499 = lean_box(0);
x_500 = x_538;
goto block_537;
}
block_537:
{
lean_object* x_501; 
lean_inc(x_2);
x_501 = l_Lean_MVarId_getType(x_2, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
lean_dec_ref(x_501);
x_503 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_493);
x_504 = l_Lean_Meta_mkAbsurd(x_502, x_498, x_503, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
lean_dec_ref(x_504);
x_506 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_505, x_493);
lean_dec(x_493);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; 
lean_dec_ref(x_506);
x_507 = lean_box(x_12);
if (x_500 == 0)
{
lean_ctor_set(x_499, 0, x_507);
x_508 = x_499;
goto block_511;
}
else
{
lean_object* x_512; 
x_512 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_512, 0, x_507);
x_508 = x_512;
goto block_511;
}
block_511:
{
lean_object* x_509; lean_object* x_510; 
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_35);
x_510 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_510, 0, x_509);
x_17 = x_510;
goto block_23;
}
}
else
{
lean_object* x_513; lean_object* x_514; uint8_t x_515; uint8_t x_520; 
lean_del_object(x_499);
lean_del_object(x_15);
lean_dec(x_14);
x_513 = lean_ctor_get(x_506, 0);
x_520 = !lean_is_exclusive(x_506);
if (x_520 == 0)
{
x_514 = x_506;
x_515 = x_520;
goto block_519;
}
else
{
lean_inc(x_513);
lean_dec(x_506);
x_514 = lean_box(0);
x_515 = x_520;
goto block_519;
}
block_519:
{
lean_object* x_516; 
if (x_515 == 0)
{
x_516 = x_514;
goto block_517;
}
else
{
lean_object* x_518; 
x_518 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_518, 0, x_513);
x_516 = x_518;
goto block_517;
}
block_517:
{
return x_516;
}
}
}
}
else
{
lean_object* x_521; lean_object* x_522; uint8_t x_523; uint8_t x_528; 
lean_del_object(x_499);
lean_dec(x_493);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_521 = lean_ctor_get(x_504, 0);
x_528 = !lean_is_exclusive(x_504);
if (x_528 == 0)
{
x_522 = x_504;
x_523 = x_528;
goto block_527;
}
else
{
lean_inc(x_521);
lean_dec(x_504);
x_522 = lean_box(0);
x_523 = x_528;
goto block_527;
}
block_527:
{
lean_object* x_524; 
if (x_523 == 0)
{
x_524 = x_522;
goto block_525;
}
else
{
lean_object* x_526; 
x_526 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_526, 0, x_521);
x_524 = x_526;
goto block_525;
}
block_525:
{
return x_524;
}
}
}
}
else
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; uint8_t x_536; 
lean_del_object(x_499);
lean_dec(x_498);
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_529 = lean_ctor_get(x_501, 0);
x_536 = !lean_is_exclusive(x_501);
if (x_536 == 0)
{
x_530 = x_501;
x_531 = x_536;
goto block_535;
}
else
{
lean_inc(x_529);
lean_dec(x_501);
x_530 = lean_box(0);
x_531 = x_536;
goto block_535;
}
block_535:
{
lean_object* x_532; 
if (x_531 == 0)
{
x_532 = x_530;
goto block_533;
}
else
{
lean_object* x_534; 
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_529);
x_532 = x_534;
goto block_533;
}
block_533:
{
return x_532;
}
}
}
}
}
else
{
lean_object* x_539; 
lean_dec(x_497);
lean_inc(x_495);
lean_inc_ref(x_494);
lean_inc(x_493);
lean_inc_ref(x_492);
lean_inc_ref(x_151);
x_539 = l_Lean_Meta_matchNe_x3f(x_151, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
lean_dec_ref(x_539);
if (lean_obj_tag(x_540) == 1)
{
lean_object* x_541; lean_object* x_542; uint8_t x_543; uint8_t x_611; 
x_541 = lean_ctor_get(x_540, 0);
x_611 = !lean_is_exclusive(x_540);
if (x_611 == 0)
{
x_542 = x_540;
x_543 = x_611;
goto block_610;
}
else
{
lean_inc(x_541);
lean_dec(x_540);
x_542 = lean_box(0);
x_543 = x_611;
goto block_610;
}
block_610:
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; uint8_t x_609; 
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
lean_dec(x_541);
x_545 = lean_ctor_get(x_544, 0);
x_546 = lean_ctor_get(x_544, 1);
x_609 = !lean_is_exclusive(x_544);
if (x_609 == 0)
{
x_547 = x_544;
x_548 = x_609;
goto block_608;
}
else
{
lean_inc(x_546);
lean_inc(x_545);
lean_dec(x_544);
x_547 = lean_box(0);
x_548 = x_609;
goto block_608;
}
block_608:
{
lean_object* x_549; 
lean_inc(x_495);
lean_inc_ref(x_494);
lean_inc(x_493);
lean_inc_ref(x_492);
lean_inc(x_545);
x_549 = l_Lean_Meta_isExprDefEq(x_545, x_546, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; uint8_t x_551; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
lean_dec_ref(x_549);
x_551 = lean_unbox(x_550);
lean_dec(x_550);
if (x_551 == 0)
{
lean_del_object(x_547);
lean_dec(x_545);
lean_del_object(x_542);
x_446 = x_492;
x_447 = x_493;
x_448 = x_494;
x_449 = x_495;
goto block_491;
}
else
{
lean_object* x_552; 
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_552 = l_Lean_MVarId_getType(x_2, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
lean_dec_ref(x_552);
lean_inc(x_495);
lean_inc_ref(x_494);
lean_inc(x_493);
lean_inc_ref(x_492);
x_554 = l_Lean_Meta_mkEqRefl(x_545, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
lean_dec_ref(x_554);
x_556 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_493);
x_557 = l_Lean_Meta_mkAbsurd(x_553, x_555, x_556, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
lean_dec_ref(x_557);
x_559 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_558, x_493);
lean_dec(x_493);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; 
lean_dec_ref(x_559);
x_560 = lean_box(x_12);
if (x_543 == 0)
{
lean_ctor_set(x_542, 0, x_560);
x_561 = x_542;
goto block_566;
}
else
{
lean_object* x_567; 
x_567 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_567, 0, x_560);
x_561 = x_567;
goto block_566;
}
block_566:
{
lean_object* x_562; 
if (x_548 == 0)
{
lean_ctor_set(x_547, 1, x_35);
lean_ctor_set(x_547, 0, x_561);
x_562 = x_547;
goto block_564;
}
else
{
lean_object* x_565; 
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_561);
lean_ctor_set(x_565, 1, x_35);
x_562 = x_565;
goto block_564;
}
block_564:
{
lean_object* x_563; 
x_563 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_563, 0, x_562);
x_17 = x_563;
goto block_23;
}
}
}
else
{
lean_object* x_568; lean_object* x_569; uint8_t x_570; uint8_t x_575; 
lean_del_object(x_547);
lean_del_object(x_542);
lean_del_object(x_15);
lean_dec(x_14);
x_568 = lean_ctor_get(x_559, 0);
x_575 = !lean_is_exclusive(x_559);
if (x_575 == 0)
{
x_569 = x_559;
x_570 = x_575;
goto block_574;
}
else
{
lean_inc(x_568);
lean_dec(x_559);
x_569 = lean_box(0);
x_570 = x_575;
goto block_574;
}
block_574:
{
lean_object* x_571; 
if (x_570 == 0)
{
x_571 = x_569;
goto block_572;
}
else
{
lean_object* x_573; 
x_573 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_573, 0, x_568);
x_571 = x_573;
goto block_572;
}
block_572:
{
return x_571;
}
}
}
}
else
{
lean_object* x_576; lean_object* x_577; uint8_t x_578; uint8_t x_583; 
lean_del_object(x_547);
lean_del_object(x_542);
lean_dec(x_493);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_576 = lean_ctor_get(x_557, 0);
x_583 = !lean_is_exclusive(x_557);
if (x_583 == 0)
{
x_577 = x_557;
x_578 = x_583;
goto block_582;
}
else
{
lean_inc(x_576);
lean_dec(x_557);
x_577 = lean_box(0);
x_578 = x_583;
goto block_582;
}
block_582:
{
lean_object* x_579; 
if (x_578 == 0)
{
x_579 = x_577;
goto block_580;
}
else
{
lean_object* x_581; 
x_581 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_581, 0, x_576);
x_579 = x_581;
goto block_580;
}
block_580:
{
return x_579;
}
}
}
}
else
{
lean_object* x_584; lean_object* x_585; uint8_t x_586; uint8_t x_591; 
lean_dec(x_553);
lean_del_object(x_547);
lean_del_object(x_542);
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_584 = lean_ctor_get(x_554, 0);
x_591 = !lean_is_exclusive(x_554);
if (x_591 == 0)
{
x_585 = x_554;
x_586 = x_591;
goto block_590;
}
else
{
lean_inc(x_584);
lean_dec(x_554);
x_585 = lean_box(0);
x_586 = x_591;
goto block_590;
}
block_590:
{
lean_object* x_587; 
if (x_586 == 0)
{
x_587 = x_585;
goto block_588;
}
else
{
lean_object* x_589; 
x_589 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_589, 0, x_584);
x_587 = x_589;
goto block_588;
}
block_588:
{
return x_587;
}
}
}
}
else
{
lean_object* x_592; lean_object* x_593; uint8_t x_594; uint8_t x_599; 
lean_del_object(x_547);
lean_dec(x_545);
lean_del_object(x_542);
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_592 = lean_ctor_get(x_552, 0);
x_599 = !lean_is_exclusive(x_552);
if (x_599 == 0)
{
x_593 = x_552;
x_594 = x_599;
goto block_598;
}
else
{
lean_inc(x_592);
lean_dec(x_552);
x_593 = lean_box(0);
x_594 = x_599;
goto block_598;
}
block_598:
{
lean_object* x_595; 
if (x_594 == 0)
{
x_595 = x_593;
goto block_596;
}
else
{
lean_object* x_597; 
x_597 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_597, 0, x_592);
x_595 = x_597;
goto block_596;
}
block_596:
{
return x_595;
}
}
}
}
}
else
{
lean_object* x_600; lean_object* x_601; uint8_t x_602; uint8_t x_607; 
lean_del_object(x_547);
lean_dec(x_545);
lean_del_object(x_542);
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_600 = lean_ctor_get(x_549, 0);
x_607 = !lean_is_exclusive(x_549);
if (x_607 == 0)
{
x_601 = x_549;
x_602 = x_607;
goto block_606;
}
else
{
lean_inc(x_600);
lean_dec(x_549);
x_601 = lean_box(0);
x_602 = x_607;
goto block_606;
}
block_606:
{
lean_object* x_603; 
if (x_602 == 0)
{
x_603 = x_601;
goto block_604;
}
else
{
lean_object* x_605; 
x_605 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_605, 0, x_600);
x_603 = x_605;
goto block_604;
}
block_604:
{
return x_603;
}
}
}
}
}
}
else
{
lean_dec(x_540);
x_446 = x_492;
x_447 = x_493;
x_448 = x_494;
x_449 = x_495;
goto block_491;
}
}
else
{
lean_object* x_612; lean_object* x_613; uint8_t x_614; uint8_t x_619; 
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_612 = lean_ctor_get(x_539, 0);
x_619 = !lean_is_exclusive(x_539);
if (x_619 == 0)
{
x_613 = x_539;
x_614 = x_619;
goto block_618;
}
else
{
lean_inc(x_612);
lean_dec(x_539);
x_613 = lean_box(0);
x_614 = x_619;
goto block_618;
}
block_618:
{
lean_object* x_615; 
if (x_614 == 0)
{
x_615 = x_613;
goto block_616;
}
else
{
lean_object* x_617; 
x_617 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_617, 0, x_612);
x_615 = x_617;
goto block_616;
}
block_616:
{
return x_615;
}
}
}
}
}
else
{
lean_object* x_620; lean_object* x_621; uint8_t x_622; uint8_t x_627; 
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_620 = lean_ctor_get(x_496, 0);
x_627 = !lean_is_exclusive(x_496);
if (x_627 == 0)
{
x_621 = x_496;
x_622 = x_627;
goto block_626;
}
else
{
lean_inc(x_620);
lean_dec(x_496);
x_621 = lean_box(0);
x_622 = x_627;
goto block_626;
}
block_626:
{
lean_object* x_623; 
if (x_622 == 0)
{
x_623 = x_621;
goto block_624;
}
else
{
lean_object* x_625; 
x_625 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_625, 0, x_620);
x_623 = x_625;
goto block_624;
}
block_624:
{
return x_623;
}
}
}
}
}
else
{
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_77;
goto block_30;
}
block_76:
{
lean_object* x_40; 
lean_inc(x_2);
x_40 = l_Lean_MVarId_getType(x_2, x_36, x_38, x_37, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_38);
x_43 = l_Lean_Meta_mkNoConfusion(x_41, x_42, x_36, x_38, x_37, x_39);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_44, x_38);
lean_dec(x_38);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_45);
x_46 = lean_box(x_12);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_46);
x_47 = x_33;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_47 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_17 = x_49;
goto block_23;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_del_object(x_33);
lean_del_object(x_15);
lean_dec(x_14);
x_52 = lean_ctor_get(x_45, 0);
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
x_53 = x_45;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_67; 
lean_dec(x_38);
lean_del_object(x_33);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_60 = lean_ctor_get(x_43, 0);
x_67 = !lean_is_exclusive(x_43);
if (x_67 == 0)
{
x_61 = x_43;
x_62 = x_67;
goto block_66;
}
else
{
lean_inc(x_60);
lean_dec(x_43);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_68 = lean_ctor_get(x_40, 0);
x_75 = !lean_is_exclusive(x_40);
if (x_75 == 0)
{
x_69 = x_40;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_40);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
block_99:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_1, 0);
x_83 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
lean_inc(x_82);
lean_inc(x_2);
x_84 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_2, x_83, x_82, x_81, x_78, x_80, x_79);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_77;
goto block_30;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_87 = lean_box(x_12);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_35);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_17 = x_90;
goto block_23;
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_98; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_91 = lean_ctor_get(x_84, 0);
x_98 = !lean_is_exclusive(x_84);
if (x_98 == 0)
{
x_92 = x_84;
x_93 = x_98;
goto block_97;
}
else
{
lean_inc(x_91);
lean_dec(x_84);
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
block_105:
{
if (x_104 == 0)
{
lean_dec_ref(x_103);
lean_dec_ref(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_77;
goto block_30;
}
else
{
x_78 = x_100;
x_79 = x_101;
x_80 = x_102;
x_81 = x_103;
goto block_99;
}
}
block_112:
{
if (x_108 == 0)
{
x_78 = x_107;
x_79 = x_109;
x_80 = x_110;
x_81 = x_111;
goto block_99;
}
else
{
x_100 = x_107;
x_101 = x_109;
x_102 = x_110;
x_103 = x_111;
x_104 = x_106;
goto block_105;
}
}
block_119:
{
if (x_118 == 0)
{
x_100 = x_113;
x_101 = x_115;
x_102 = x_116;
x_103 = x_117;
x_104 = x_106;
goto block_105;
}
else
{
x_107 = x_113;
x_108 = x_114;
x_109 = x_115;
x_110 = x_116;
x_111 = x_117;
goto block_112;
}
}
block_127:
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_126 == 0)
{
x_113 = x_123;
x_114 = x_120;
x_115 = x_125;
x_116 = x_124;
x_117 = x_122;
x_118 = x_106;
goto block_119;
}
else
{
if (x_121 == 0)
{
x_107 = x_123;
x_108 = x_120;
x_109 = x_125;
x_110 = x_124;
x_111 = x_122;
goto block_112;
}
else
{
x_113 = x_123;
x_114 = x_120;
x_115 = x_125;
x_116 = x_124;
x_117 = x_122;
x_118 = x_106;
goto block_119;
}
}
}
block_150:
{
if (x_134 == 0)
{
x_120 = x_128;
x_121 = x_133;
x_122 = x_131;
x_123 = x_132;
x_124 = x_130;
x_125 = x_129;
goto block_127;
}
else
{
lean_object* x_135; 
lean_inc(x_129);
lean_inc_ref(x_130);
lean_inc(x_132);
lean_inc_ref(x_131);
lean_inc(x_32);
lean_inc(x_2);
x_135 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_2, x_32, x_131, x_132, x_130, x_129);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
x_120 = x_128;
x_121 = x_133;
x_122 = x_131;
x_123 = x_132;
x_124 = x_130;
x_125 = x_129;
goto block_127;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_138 = lean_box(x_12);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_35);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_17 = x_141;
goto block_23;
}
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; uint8_t x_149; 
lean_dec(x_132);
lean_dec_ref(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_142 = lean_ctor_get(x_135, 0);
x_149 = !lean_is_exclusive(x_135);
if (x_149 == 0)
{
x_143 = x_135;
x_144 = x_149;
goto block_148;
}
else
{
lean_inc(x_142);
lean_dec(x_135);
x_143 = lean_box(0);
x_144 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_145; 
if (x_144 == 0)
{
x_145 = x_143;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_142);
x_145 = x_147;
goto block_146;
}
block_146:
{
return x_145;
}
}
}
}
}
}
}
block_23:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_14);
x_19 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
block_30:
{
lean_object* x_26; size_t x_27; size_t x_28; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_5, x_27);
x_5 = x_28;
x_6 = x_26;
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
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_702; 
x_14 = lean_ctor_get(x_6, 1);
x_702 = !lean_is_exclusive(x_6);
if (x_702 == 0)
{
lean_object* x_703; 
x_703 = lean_ctor_get(x_6, 0);
lean_dec(x_703);
x_15 = x_6;
x_16 = x_702;
goto block_701;
}
else
{
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = x_702;
goto block_701;
}
block_701:
{
lean_object* x_17; lean_object* x_24; lean_object* x_25; lean_object* x_31; 
x_24 = lean_box(0);
x_31 = lean_array_uget(x_3, x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_del_object(x_15);
x_25 = x_14;
goto block_30;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_700; 
x_32 = lean_ctor_get(x_31, 0);
x_700 = !lean_is_exclusive(x_31);
if (x_700 == 0)
{
x_33 = x_31;
x_34 = x_700;
goto block_699;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_700;
goto block_699;
}
block_699:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_35 = lean_box(0);
x_77 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
x_106 = l_Lean_LocalDecl_isImplementationDetail(x_32);
if (x_106 == 0)
{
lean_object* x_151; uint8_t x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; uint8_t x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; uint8_t x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; uint8_t x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_629; 
x_151 = l_Lean_LocalDecl_type(x_32);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_151);
x_629 = l_Lean_Meta_matchNot_x3f(x_151, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
lean_dec_ref(x_629);
if (lean_obj_tag(x_630) == 1)
{
lean_object* x_631; lean_object* x_632; uint8_t x_633; uint8_t x_690; 
x_631 = lean_ctor_get(x_630, 0);
x_690 = !lean_is_exclusive(x_630);
if (x_690 == 0)
{
x_632 = x_630;
x_633 = x_690;
goto block_689;
}
else
{
lean_inc(x_631);
lean_dec(x_630);
x_632 = lean_box(0);
x_633 = x_690;
goto block_689;
}
block_689:
{
lean_object* x_634; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_634 = l_Lean_Meta_findLocalDeclWithType_x3f(x_631, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
lean_dec_ref(x_634);
if (lean_obj_tag(x_635) == 1)
{
lean_object* x_636; lean_object* x_637; uint8_t x_638; uint8_t x_680; 
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec_ref(x_1);
x_636 = lean_ctor_get(x_635, 0);
x_680 = !lean_is_exclusive(x_635);
if (x_680 == 0)
{
x_637 = x_635;
x_638 = x_680;
goto block_679;
}
else
{
lean_inc(x_636);
lean_dec(x_635);
x_637 = lean_box(0);
x_638 = x_680;
goto block_679;
}
block_679:
{
lean_object* x_639; 
lean_inc(x_2);
x_639 = l_Lean_MVarId_getType(x_2, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
lean_dec_ref(x_639);
x_641 = l_Lean_LocalDecl_toExpr(x_32);
x_642 = l_Lean_mkFVar(x_636);
x_643 = l_Lean_Expr_app___override(x_641, x_642);
lean_inc(x_8);
x_644 = l_Lean_Meta_mkFalseElim(x_640, x_643, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; 
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
lean_dec_ref(x_644);
x_646 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_645, x_8);
lean_dec(x_8);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; 
lean_dec_ref(x_646);
x_647 = lean_box(x_12);
if (x_638 == 0)
{
lean_ctor_set(x_637, 0, x_647);
x_648 = x_637;
goto block_653;
}
else
{
lean_object* x_654; 
x_654 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_654, 0, x_647);
x_648 = x_654;
goto block_653;
}
block_653:
{
lean_object* x_649; lean_object* x_650; 
x_649 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_649, 0, x_648);
lean_ctor_set(x_649, 1, x_35);
if (x_633 == 0)
{
lean_ctor_set_tag(x_632, 0);
lean_ctor_set(x_632, 0, x_649);
x_650 = x_632;
goto block_651;
}
else
{
lean_object* x_652; 
x_652 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_652, 0, x_649);
x_650 = x_652;
goto block_651;
}
block_651:
{
x_17 = x_650;
goto block_23;
}
}
}
else
{
lean_object* x_655; lean_object* x_656; uint8_t x_657; uint8_t x_662; 
lean_del_object(x_637);
lean_del_object(x_632);
lean_del_object(x_15);
lean_dec(x_14);
x_655 = lean_ctor_get(x_646, 0);
x_662 = !lean_is_exclusive(x_646);
if (x_662 == 0)
{
x_656 = x_646;
x_657 = x_662;
goto block_661;
}
else
{
lean_inc(x_655);
lean_dec(x_646);
x_656 = lean_box(0);
x_657 = x_662;
goto block_661;
}
block_661:
{
lean_object* x_658; 
if (x_657 == 0)
{
x_658 = x_656;
goto block_659;
}
else
{
lean_object* x_660; 
x_660 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_660, 0, x_655);
x_658 = x_660;
goto block_659;
}
block_659:
{
return x_658;
}
}
}
}
else
{
lean_object* x_663; lean_object* x_664; uint8_t x_665; uint8_t x_670; 
lean_del_object(x_637);
lean_del_object(x_632);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_2);
x_663 = lean_ctor_get(x_644, 0);
x_670 = !lean_is_exclusive(x_644);
if (x_670 == 0)
{
x_664 = x_644;
x_665 = x_670;
goto block_669;
}
else
{
lean_inc(x_663);
lean_dec(x_644);
x_664 = lean_box(0);
x_665 = x_670;
goto block_669;
}
block_669:
{
lean_object* x_666; 
if (x_665 == 0)
{
x_666 = x_664;
goto block_667;
}
else
{
lean_object* x_668; 
x_668 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_668, 0, x_663);
x_666 = x_668;
goto block_667;
}
block_667:
{
return x_666;
}
}
}
}
else
{
lean_object* x_671; lean_object* x_672; uint8_t x_673; uint8_t x_678; 
lean_del_object(x_637);
lean_dec(x_636);
lean_del_object(x_632);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
x_671 = lean_ctor_get(x_639, 0);
x_678 = !lean_is_exclusive(x_639);
if (x_678 == 0)
{
x_672 = x_639;
x_673 = x_678;
goto block_677;
}
else
{
lean_inc(x_671);
lean_dec(x_639);
x_672 = lean_box(0);
x_673 = x_678;
goto block_677;
}
block_677:
{
lean_object* x_674; 
if (x_673 == 0)
{
x_674 = x_672;
goto block_675;
}
else
{
lean_object* x_676; 
x_676 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_676, 0, x_671);
x_674 = x_676;
goto block_675;
}
block_675:
{
return x_674;
}
}
}
}
}
else
{
lean_dec(x_635);
lean_del_object(x_632);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_492 = x_7;
x_493 = x_8;
x_494 = x_9;
x_495 = x_10;
goto block_628;
}
}
else
{
lean_object* x_681; lean_object* x_682; uint8_t x_683; uint8_t x_688; 
lean_del_object(x_632);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_681 = lean_ctor_get(x_634, 0);
x_688 = !lean_is_exclusive(x_634);
if (x_688 == 0)
{
x_682 = x_634;
x_683 = x_688;
goto block_687;
}
else
{
lean_inc(x_681);
lean_dec(x_634);
x_682 = lean_box(0);
x_683 = x_688;
goto block_687;
}
block_687:
{
lean_object* x_684; 
if (x_683 == 0)
{
x_684 = x_682;
goto block_685;
}
else
{
lean_object* x_686; 
x_686 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_686, 0, x_681);
x_684 = x_686;
goto block_685;
}
block_685:
{
return x_684;
}
}
}
}
}
else
{
lean_dec(x_630);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_492 = x_7;
x_493 = x_8;
x_494 = x_9;
x_495 = x_10;
goto block_628;
}
}
else
{
lean_object* x_691; lean_object* x_692; uint8_t x_693; uint8_t x_698; 
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_691 = lean_ctor_get(x_629, 0);
x_698 = !lean_is_exclusive(x_629);
if (x_698 == 0)
{
x_692 = x_629;
x_693 = x_698;
goto block_697;
}
else
{
lean_inc(x_691);
lean_dec(x_629);
x_692 = lean_box(0);
x_693 = x_698;
goto block_697;
}
block_697:
{
lean_object* x_694; 
if (x_693 == 0)
{
x_694 = x_692;
goto block_695;
}
else
{
lean_object* x_696; 
x_696 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_696, 0, x_691);
x_694 = x_696;
goto block_695;
}
block_695:
{
return x_694;
}
}
}
block_160:
{
uint8_t x_158; 
x_158 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 2);
if (x_158 == 0)
{
lean_dec_ref(x_151);
x_128 = x_152;
x_129 = x_153;
x_130 = x_155;
x_131 = x_156;
x_132 = x_154;
x_133 = x_157;
x_134 = x_106;
goto block_150;
}
else
{
uint8_t x_159; 
x_159 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_151);
x_128 = x_152;
x_129 = x_153;
x_130 = x_155;
x_131 = x_156;
x_132 = x_154;
x_133 = x_157;
x_134 = x_159;
goto block_150;
}
}
block_170:
{
if (x_168 == 0)
{
lean_dec_ref(x_162);
x_152 = x_161;
x_153 = x_163;
x_154 = x_167;
x_155 = x_165;
x_156 = x_166;
x_157 = x_164;
goto block_160;
}
else
{
lean_object* x_169; 
lean_dec_ref(x_167);
lean_dec_ref(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_162);
return x_169;
}
}
block_180:
{
uint8_t x_178; 
x_178 = l_Lean_Exception_isInterrupt(x_177);
if (x_178 == 0)
{
uint8_t x_179; 
lean_inc_ref(x_177);
x_179 = l_Lean_Exception_isRuntime(x_177);
x_161 = x_171;
x_162 = x_177;
x_163 = x_172;
x_164 = x_174;
x_165 = x_173;
x_166 = x_176;
x_167 = x_175;
x_168 = x_179;
goto block_170;
}
else
{
x_161 = x_171;
x_162 = x_177;
x_163 = x_172;
x_164 = x_174;
x_165 = x_173;
x_166 = x_176;
x_167 = x_175;
x_168 = x_178;
goto block_170;
}
}
block_278:
{
lean_object* x_187; 
lean_inc(x_183);
lean_inc_ref(x_185);
lean_inc(x_184);
lean_inc_ref(x_186);
lean_inc_ref(x_151);
x_187 = l_Lean_Meta_mkDecide(x_151, x_186, x_184, x_185, x_183);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; lean_object* x_208; uint8_t x_209; uint8_t x_276; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_189 = l_Lean_Meta_Context_config(x_186);
x_190 = lean_ctor_get_uint8(x_189, 0);
x_191 = lean_ctor_get_uint8(x_189, 1);
x_192 = lean_ctor_get_uint8(x_189, 2);
x_193 = lean_ctor_get_uint8(x_189, 3);
x_194 = lean_ctor_get_uint8(x_189, 4);
x_195 = lean_ctor_get_uint8(x_189, 5);
x_196 = lean_ctor_get_uint8(x_189, 6);
x_197 = lean_ctor_get_uint8(x_189, 7);
x_198 = lean_ctor_get_uint8(x_189, 8);
x_199 = lean_ctor_get_uint8(x_189, 10);
x_200 = lean_ctor_get_uint8(x_189, 11);
x_201 = lean_ctor_get_uint8(x_189, 12);
x_202 = lean_ctor_get_uint8(x_189, 13);
x_203 = lean_ctor_get_uint8(x_189, 14);
x_204 = lean_ctor_get_uint8(x_189, 15);
x_205 = lean_ctor_get_uint8(x_189, 16);
x_206 = lean_ctor_get_uint8(x_189, 17);
x_207 = lean_ctor_get_uint8(x_189, 18);
x_276 = !lean_is_exclusive(x_189);
if (x_276 == 0)
{
x_208 = x_189;
x_209 = x_276;
goto block_275;
}
else
{
lean_dec(x_189);
x_208 = lean_box(0);
x_209 = x_276;
goto block_275;
}
block_275:
{
uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; lean_object* x_221; 
x_210 = lean_ctor_get_uint8(x_186, sizeof(void*)*7);
x_211 = lean_ctor_get(x_186, 1);
x_212 = lean_ctor_get(x_186, 2);
x_213 = lean_ctor_get(x_186, 3);
x_214 = lean_ctor_get(x_186, 4);
x_215 = lean_ctor_get(x_186, 5);
x_216 = lean_ctor_get(x_186, 6);
x_217 = lean_ctor_get_uint8(x_186, sizeof(void*)*7 + 1);
x_218 = lean_ctor_get_uint8(x_186, sizeof(void*)*7 + 2);
x_219 = lean_ctor_get_uint8(x_186, sizeof(void*)*7 + 3);
x_220 = 1;
if (x_209 == 0)
{
x_221 = x_208;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_274, 0, x_190);
lean_ctor_set_uint8(x_274, 1, x_191);
lean_ctor_set_uint8(x_274, 2, x_192);
lean_ctor_set_uint8(x_274, 3, x_193);
lean_ctor_set_uint8(x_274, 4, x_194);
lean_ctor_set_uint8(x_274, 5, x_195);
lean_ctor_set_uint8(x_274, 6, x_196);
lean_ctor_set_uint8(x_274, 7, x_197);
lean_ctor_set_uint8(x_274, 8, x_198);
lean_ctor_set_uint8(x_274, 10, x_199);
lean_ctor_set_uint8(x_274, 11, x_200);
lean_ctor_set_uint8(x_274, 12, x_201);
lean_ctor_set_uint8(x_274, 13, x_202);
lean_ctor_set_uint8(x_274, 14, x_203);
lean_ctor_set_uint8(x_274, 15, x_204);
lean_ctor_set_uint8(x_274, 16, x_205);
lean_ctor_set_uint8(x_274, 17, x_206);
lean_ctor_set_uint8(x_274, 18, x_207);
x_221 = x_274;
goto block_273;
}
block_273:
{
uint64_t x_222; uint64_t x_223; uint64_t x_224; uint64_t x_225; uint64_t x_226; uint64_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_ctor_set_uint8(x_221, 9, x_220);
x_222 = l_Lean_Meta_Context_configKey(x_186);
x_223 = 2;
x_224 = lean_uint64_shift_right(x_222, x_223);
x_225 = lean_uint64_shift_left(x_224, x_223);
x_226 = lean_uint64_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1);
x_227 = lean_uint64_lor(x_225, x_226);
x_228 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_228, 0, x_221);
lean_ctor_set_uint64(x_228, sizeof(void*)*1, x_227);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc_ref(x_213);
lean_inc_ref(x_212);
lean_inc(x_211);
x_229 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_211);
lean_ctor_set(x_229, 2, x_212);
lean_ctor_set(x_229, 3, x_213);
lean_ctor_set(x_229, 4, x_214);
lean_ctor_set(x_229, 5, x_215);
lean_ctor_set(x_229, 6, x_216);
lean_ctor_set_uint8(x_229, sizeof(void*)*7, x_210);
lean_ctor_set_uint8(x_229, sizeof(void*)*7 + 1, x_217);
lean_ctor_set_uint8(x_229, sizeof(void*)*7 + 2, x_218);
lean_ctor_set_uint8(x_229, sizeof(void*)*7 + 3, x_219);
lean_inc(x_183);
lean_inc_ref(x_185);
lean_inc(x_184);
lean_inc(x_188);
x_230 = lean_whnf(x_188, x_229, x_184, x_185, x_183);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
lean_dec_ref(x_230);
x_232 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4));
x_233 = l_Lean_Expr_isConstOf(x_231, x_232);
lean_dec(x_231);
if (x_233 == 0)
{
lean_dec(x_188);
x_152 = x_181;
x_153 = x_182;
x_154 = x_186;
x_155 = x_184;
x_156 = x_185;
x_157 = x_183;
goto block_160;
}
else
{
lean_object* x_234; 
lean_inc(x_183);
lean_inc_ref(x_185);
lean_inc(x_184);
lean_inc_ref(x_186);
lean_inc(x_188);
x_234 = l_Lean_Meta_mkEqRefl(x_188, x_186, x_184, x_185, x_183);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec_ref(x_234);
lean_inc(x_2);
x_236 = l_Lean_MVarId_getType(x_2, x_186, x_184, x_185, x_183);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec_ref(x_236);
x_238 = l_Lean_Expr_getAppNumArgs(x_188);
x_239 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
x_240 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__8);
lean_inc(x_238);
x_241 = lean_mk_array(x_238, x_240);
x_242 = lean_unsigned_to_nat(1u);
x_243 = lean_nat_sub(x_238, x_242);
lean_dec(x_238);
x_244 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_188, x_241, x_243);
x_245 = lean_array_push(x_244, x_235);
x_246 = l_Lean_mkAppN(x_239, x_245);
lean_dec_ref(x_245);
lean_inc(x_32);
x_247 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_183);
lean_inc_ref(x_185);
lean_inc(x_184);
lean_inc_ref(x_186);
x_248 = l_Lean_Meta_mkAbsurd(x_237, x_247, x_246, x_186, x_184, x_185, x_183);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_268; 
x_249 = lean_ctor_get(x_248, 0);
x_268 = !lean_is_exclusive(x_248);
if (x_268 == 0)
{
x_250 = x_248;
x_251 = x_268;
goto block_267;
}
else
{
lean_inc(x_249);
lean_dec(x_248);
x_250 = lean_box(0);
x_251 = x_268;
goto block_267;
}
block_267:
{
lean_object* x_252; 
lean_inc(x_2);
x_252 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_249, x_184);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; uint8_t x_254; uint8_t x_264; 
lean_dec_ref(x_186);
lean_dec_ref(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_264 = !lean_is_exclusive(x_252);
if (x_264 == 0)
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_252, 0);
lean_dec(x_265);
x_253 = x_252;
x_254 = x_264;
goto block_263;
}
else
{
lean_dec(x_252);
x_253 = lean_box(0);
x_254 = x_264;
goto block_263;
}
block_263:
{
lean_object* x_255; lean_object* x_256; 
x_255 = lean_box(x_12);
if (x_254 == 0)
{
lean_ctor_set_tag(x_253, 1);
lean_ctor_set(x_253, 0, x_255);
x_256 = x_253;
goto block_261;
}
else
{
lean_object* x_262; 
x_262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_262, 0, x_255);
x_256 = x_262;
goto block_261;
}
block_261:
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_35);
if (x_251 == 0)
{
lean_ctor_set(x_250, 0, x_257);
x_258 = x_250;
goto block_259;
}
else
{
lean_object* x_260; 
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_257);
x_258 = x_260;
goto block_259;
}
block_259:
{
x_17 = x_258;
goto block_23;
}
}
}
}
else
{
lean_object* x_266; 
lean_del_object(x_250);
x_266 = lean_ctor_get(x_252, 0);
lean_inc(x_266);
lean_dec_ref(x_252);
x_171 = x_181;
x_172 = x_182;
x_173 = x_184;
x_174 = x_183;
x_175 = x_186;
x_176 = x_185;
x_177 = x_266;
goto block_180;
}
}
}
else
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_248, 0);
lean_inc(x_269);
lean_dec_ref(x_248);
x_171 = x_181;
x_172 = x_182;
x_173 = x_184;
x_174 = x_183;
x_175 = x_186;
x_176 = x_185;
x_177 = x_269;
goto block_180;
}
}
else
{
lean_object* x_270; 
lean_dec(x_235);
lean_dec(x_188);
x_270 = lean_ctor_get(x_236, 0);
lean_inc(x_270);
lean_dec_ref(x_236);
x_171 = x_181;
x_172 = x_182;
x_173 = x_184;
x_174 = x_183;
x_175 = x_186;
x_176 = x_185;
x_177 = x_270;
goto block_180;
}
}
else
{
lean_object* x_271; 
lean_dec(x_188);
x_271 = lean_ctor_get(x_234, 0);
lean_inc(x_271);
lean_dec_ref(x_234);
x_171 = x_181;
x_172 = x_182;
x_173 = x_184;
x_174 = x_183;
x_175 = x_186;
x_176 = x_185;
x_177 = x_271;
goto block_180;
}
}
}
else
{
lean_object* x_272; 
lean_dec(x_188);
x_272 = lean_ctor_get(x_230, 0);
lean_inc(x_272);
lean_dec_ref(x_230);
x_171 = x_181;
x_172 = x_182;
x_173 = x_184;
x_174 = x_183;
x_175 = x_186;
x_176 = x_185;
x_177 = x_272;
goto block_180;
}
}
}
}
else
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_187, 0);
lean_inc(x_277);
lean_dec_ref(x_187);
x_171 = x_181;
x_172 = x_182;
x_173 = x_184;
x_174 = x_183;
x_175 = x_186;
x_176 = x_185;
x_177 = x_277;
goto block_180;
}
}
block_286:
{
if (x_285 == 0)
{
x_152 = x_279;
x_153 = x_280;
x_154 = x_284;
x_155 = x_282;
x_156 = x_283;
x_157 = x_281;
goto block_160;
}
else
{
x_181 = x_279;
x_182 = x_280;
x_183 = x_281;
x_184 = x_282;
x_185 = x_283;
x_186 = x_284;
goto block_278;
}
}
block_296:
{
if (x_294 == 0)
{
lean_dec_ref(x_293);
x_279 = x_287;
x_280 = x_288;
x_281 = x_290;
x_282 = x_289;
x_283 = x_292;
x_284 = x_291;
x_285 = x_106;
goto block_286;
}
else
{
uint8_t x_295; 
x_295 = l_Lean_Expr_hasFVar(x_293);
lean_dec_ref(x_293);
if (x_295 == 0)
{
x_181 = x_287;
x_182 = x_288;
x_183 = x_290;
x_184 = x_289;
x_185 = x_292;
x_186 = x_291;
goto block_278;
}
else
{
x_279 = x_287;
x_280 = x_288;
x_281 = x_290;
x_282 = x_289;
x_283 = x_292;
x_284 = x_291;
x_285 = x_106;
goto block_286;
}
}
}
block_315:
{
lean_object* x_304; 
lean_inc_ref(x_151);
x_304 = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(x_151, x_300);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; uint8_t x_306; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
lean_dec_ref(x_304);
x_306 = l_Lean_Expr_hasMVar(x_305);
if (x_306 == 0)
{
x_287 = x_297;
x_288 = x_298;
x_289 = x_300;
x_290 = x_299;
x_291 = x_301;
x_292 = x_302;
x_293 = x_305;
x_294 = x_303;
goto block_296;
}
else
{
x_287 = x_297;
x_288 = x_298;
x_289 = x_300;
x_290 = x_299;
x_291 = x_301;
x_292 = x_302;
x_293 = x_305;
x_294 = x_106;
goto block_296;
}
}
else
{
lean_object* x_307; lean_object* x_308; uint8_t x_309; uint8_t x_314; 
lean_dec_ref(x_302);
lean_dec_ref(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_307 = lean_ctor_get(x_304, 0);
x_314 = !lean_is_exclusive(x_304);
if (x_314 == 0)
{
x_308 = x_304;
x_309 = x_314;
goto block_313;
}
else
{
lean_inc(x_307);
lean_dec(x_304);
x_308 = lean_box(0);
x_309 = x_314;
goto block_313;
}
block_313:
{
lean_object* x_310; 
if (x_309 == 0)
{
x_310 = x_308;
goto block_311;
}
else
{
lean_object* x_312; 
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_307);
x_310 = x_312;
goto block_311;
}
block_311:
{
return x_310;
}
}
}
}
block_323:
{
if (x_322 == 0)
{
x_152 = x_316;
x_153 = x_317;
x_154 = x_321;
x_155 = x_319;
x_156 = x_320;
x_157 = x_318;
goto block_160;
}
else
{
x_297 = x_316;
x_298 = x_317;
x_299 = x_318;
x_300 = x_319;
x_301 = x_321;
x_302 = x_320;
x_303 = x_322;
goto block_315;
}
}
block_332:
{
uint8_t x_330; 
x_330 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
if (x_330 == 0)
{
x_316 = x_324;
x_317 = x_325;
x_318 = x_329;
x_319 = x_327;
x_320 = x_328;
x_321 = x_326;
x_322 = x_106;
goto block_323;
}
else
{
uint8_t x_331; 
x_331 = l_Lean_Expr_hasFVar(x_151);
if (x_331 == 0)
{
x_297 = x_324;
x_298 = x_325;
x_299 = x_329;
x_300 = x_327;
x_301 = x_326;
x_302 = x_328;
x_303 = x_330;
goto block_315;
}
else
{
x_316 = x_324;
x_317 = x_325;
x_318 = x_329;
x_319 = x_327;
x_320 = x_328;
x_321 = x_326;
x_322 = x_106;
goto block_323;
}
}
}
block_395:
{
lean_object* x_340; 
lean_inc(x_335);
lean_inc_ref(x_336);
lean_inc(x_338);
lean_inc_ref(x_339);
x_340 = l_Lean_Meta_isExprDefEq(x_334, x_337, x_339, x_338, x_336, x_335);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; uint8_t x_342; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
lean_dec_ref(x_340);
x_342 = lean_unbox(x_341);
lean_dec(x_341);
if (x_342 == 0)
{
x_324 = x_333;
x_325 = x_12;
x_326 = x_339;
x_327 = x_338;
x_328 = x_336;
x_329 = x_335;
goto block_332;
}
else
{
lean_object* x_343; 
lean_dec_ref(x_151);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_343 = l_Lean_MVarId_getType(x_2, x_339, x_338, x_336, x_335);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec_ref(x_343);
x_345 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_335);
lean_inc_ref(x_336);
lean_inc(x_338);
lean_inc_ref(x_339);
x_346 = l_Lean_Meta_mkEqOfHEq(x_345, x_12, x_339, x_338, x_336, x_335);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
lean_dec_ref(x_346);
lean_inc(x_338);
x_348 = l_Lean_Meta_mkNoConfusion(x_344, x_347, x_339, x_338, x_336, x_335);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
lean_dec_ref(x_348);
x_350 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_349, x_338);
lean_dec(x_338);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec_ref(x_350);
x_351 = lean_box(x_12);
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_351);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_35);
x_354 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_354, 0, x_353);
x_17 = x_354;
goto block_23;
}
else
{
lean_object* x_355; lean_object* x_356; uint8_t x_357; uint8_t x_362; 
lean_del_object(x_15);
lean_dec(x_14);
x_355 = lean_ctor_get(x_350, 0);
x_362 = !lean_is_exclusive(x_350);
if (x_362 == 0)
{
x_356 = x_350;
x_357 = x_362;
goto block_361;
}
else
{
lean_inc(x_355);
lean_dec(x_350);
x_356 = lean_box(0);
x_357 = x_362;
goto block_361;
}
block_361:
{
lean_object* x_358; 
if (x_357 == 0)
{
x_358 = x_356;
goto block_359;
}
else
{
lean_object* x_360; 
x_360 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_360, 0, x_355);
x_358 = x_360;
goto block_359;
}
block_359:
{
return x_358;
}
}
}
}
else
{
lean_object* x_363; lean_object* x_364; uint8_t x_365; uint8_t x_370; 
lean_dec(x_338);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_363 = lean_ctor_get(x_348, 0);
x_370 = !lean_is_exclusive(x_348);
if (x_370 == 0)
{
x_364 = x_348;
x_365 = x_370;
goto block_369;
}
else
{
lean_inc(x_363);
lean_dec(x_348);
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
lean_dec(x_344);
lean_dec_ref(x_339);
lean_dec(x_338);
lean_dec_ref(x_336);
lean_dec(x_335);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_371 = lean_ctor_get(x_346, 0);
x_378 = !lean_is_exclusive(x_346);
if (x_378 == 0)
{
x_372 = x_346;
x_373 = x_378;
goto block_377;
}
else
{
lean_inc(x_371);
lean_dec(x_346);
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
lean_dec_ref(x_339);
lean_dec(x_338);
lean_dec_ref(x_336);
lean_dec(x_335);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_379 = lean_ctor_get(x_343, 0);
x_386 = !lean_is_exclusive(x_343);
if (x_386 == 0)
{
x_380 = x_343;
x_381 = x_386;
goto block_385;
}
else
{
lean_inc(x_379);
lean_dec(x_343);
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
}
else
{
lean_object* x_387; lean_object* x_388; uint8_t x_389; uint8_t x_394; 
lean_dec_ref(x_339);
lean_dec(x_338);
lean_dec_ref(x_336);
lean_dec(x_335);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_387 = lean_ctor_get(x_340, 0);
x_394 = !lean_is_exclusive(x_340);
if (x_394 == 0)
{
x_388 = x_340;
x_389 = x_394;
goto block_393;
}
else
{
lean_inc(x_387);
lean_dec(x_340);
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
block_445:
{
lean_object* x_401; 
lean_inc(x_400);
lean_inc_ref(x_399);
lean_inc(x_398);
lean_inc_ref(x_397);
lean_inc_ref(x_151);
x_401 = l_Lean_Meta_matchHEq_x3f(x_151, x_397, x_398, x_399, x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
lean_dec_ref(x_401);
if (lean_obj_tag(x_402) == 1)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
lean_dec_ref(x_402);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_404, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_403, 0);
lean_inc(x_406);
lean_dec(x_403);
x_407 = lean_ctor_get(x_404, 0);
lean_inc(x_407);
lean_dec(x_404);
x_408 = lean_ctor_get(x_405, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_405, 1);
lean_inc(x_409);
lean_dec(x_405);
lean_inc(x_400);
lean_inc_ref(x_399);
lean_inc(x_398);
lean_inc_ref(x_397);
x_410 = l_Lean_Meta_matchConstructorApp_x3f(x_407, x_397, x_398, x_399, x_400);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
lean_dec_ref(x_410);
if (lean_obj_tag(x_411) == 1)
{
lean_object* x_412; lean_object* x_413; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
lean_dec_ref(x_411);
lean_inc(x_400);
lean_inc_ref(x_399);
lean_inc(x_398);
lean_inc_ref(x_397);
x_413 = l_Lean_Meta_matchConstructorApp_x3f(x_409, x_397, x_398, x_399, x_400);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
lean_dec_ref(x_413);
if (lean_obj_tag(x_414) == 1)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_415 = lean_ctor_get(x_412, 0);
lean_inc_ref(x_415);
lean_dec(x_412);
x_416 = lean_ctor_get(x_414, 0);
lean_inc(x_416);
lean_dec_ref(x_414);
x_417 = lean_ctor_get(x_416, 0);
lean_inc_ref(x_417);
lean_dec(x_416);
x_418 = lean_ctor_get(x_415, 0);
lean_inc(x_418);
lean_dec_ref(x_415);
x_419 = lean_ctor_get(x_417, 0);
lean_inc(x_419);
lean_dec_ref(x_417);
x_420 = lean_name_eq(x_418, x_419);
lean_dec(x_419);
lean_dec(x_418);
if (x_420 == 0)
{
x_333 = x_396;
x_334 = x_406;
x_335 = x_400;
x_336 = x_399;
x_337 = x_408;
x_338 = x_398;
x_339 = x_397;
goto block_395;
}
else
{
if (x_106 == 0)
{
lean_dec(x_408);
lean_dec(x_406);
x_324 = x_396;
x_325 = x_12;
x_326 = x_397;
x_327 = x_398;
x_328 = x_399;
x_329 = x_400;
goto block_332;
}
else
{
x_333 = x_396;
x_334 = x_406;
x_335 = x_400;
x_336 = x_399;
x_337 = x_408;
x_338 = x_398;
x_339 = x_397;
goto block_395;
}
}
}
else
{
lean_dec(x_414);
lean_dec(x_412);
lean_dec(x_408);
lean_dec(x_406);
x_324 = x_396;
x_325 = x_12;
x_326 = x_397;
x_327 = x_398;
x_328 = x_399;
x_329 = x_400;
goto block_332;
}
}
else
{
lean_object* x_421; lean_object* x_422; uint8_t x_423; uint8_t x_428; 
lean_dec(x_412);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_400);
lean_dec_ref(x_399);
lean_dec(x_398);
lean_dec_ref(x_397);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_421 = lean_ctor_get(x_413, 0);
x_428 = !lean_is_exclusive(x_413);
if (x_428 == 0)
{
x_422 = x_413;
x_423 = x_428;
goto block_427;
}
else
{
lean_inc(x_421);
lean_dec(x_413);
x_422 = lean_box(0);
x_423 = x_428;
goto block_427;
}
block_427:
{
lean_object* x_424; 
if (x_423 == 0)
{
x_424 = x_422;
goto block_425;
}
else
{
lean_object* x_426; 
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_421);
x_424 = x_426;
goto block_425;
}
block_425:
{
return x_424;
}
}
}
}
else
{
lean_dec(x_411);
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_406);
x_324 = x_396;
x_325 = x_12;
x_326 = x_397;
x_327 = x_398;
x_328 = x_399;
x_329 = x_400;
goto block_332;
}
}
else
{
lean_object* x_429; lean_object* x_430; uint8_t x_431; uint8_t x_436; 
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_400);
lean_dec_ref(x_399);
lean_dec(x_398);
lean_dec_ref(x_397);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_429 = lean_ctor_get(x_410, 0);
x_436 = !lean_is_exclusive(x_410);
if (x_436 == 0)
{
x_430 = x_410;
x_431 = x_436;
goto block_435;
}
else
{
lean_inc(x_429);
lean_dec(x_410);
x_430 = lean_box(0);
x_431 = x_436;
goto block_435;
}
block_435:
{
lean_object* x_432; 
if (x_431 == 0)
{
x_432 = x_430;
goto block_433;
}
else
{
lean_object* x_434; 
x_434 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_434, 0, x_429);
x_432 = x_434;
goto block_433;
}
block_433:
{
return x_432;
}
}
}
}
else
{
lean_dec(x_402);
x_324 = x_396;
x_325 = x_106;
x_326 = x_397;
x_327 = x_398;
x_328 = x_399;
x_329 = x_400;
goto block_332;
}
}
else
{
lean_object* x_437; lean_object* x_438; uint8_t x_439; uint8_t x_444; 
lean_dec(x_400);
lean_dec_ref(x_399);
lean_dec(x_398);
lean_dec_ref(x_397);
lean_dec_ref(x_151);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_437 = lean_ctor_get(x_401, 0);
x_444 = !lean_is_exclusive(x_401);
if (x_444 == 0)
{
x_438 = x_401;
x_439 = x_444;
goto block_443;
}
else
{
lean_inc(x_437);
lean_dec(x_401);
x_438 = lean_box(0);
x_439 = x_444;
goto block_443;
}
block_443:
{
lean_object* x_440; 
if (x_439 == 0)
{
x_440 = x_438;
goto block_441;
}
else
{
lean_object* x_442; 
x_442 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_442, 0, x_437);
x_440 = x_442;
goto block_441;
}
block_441:
{
return x_440;
}
}
}
}
block_491:
{
lean_object* x_450; 
lean_inc(x_449);
lean_inc_ref(x_448);
lean_inc(x_447);
lean_inc_ref(x_446);
lean_inc_ref(x_151);
x_450 = l_Lean_Meta_matchEq_x3f(x_151, x_446, x_447, x_448, x_449);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
lean_dec_ref(x_450);
if (lean_obj_tag(x_451) == 1)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
lean_dec_ref(x_451);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
lean_dec(x_452);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
lean_inc(x_449);
lean_inc_ref(x_448);
lean_inc(x_447);
lean_inc_ref(x_446);
x_456 = l_Lean_Meta_matchConstructorApp_x3f(x_454, x_446, x_447, x_448, x_449);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
lean_dec_ref(x_456);
if (lean_obj_tag(x_457) == 1)
{
lean_object* x_458; lean_object* x_459; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
lean_dec_ref(x_457);
lean_inc(x_449);
lean_inc_ref(x_448);
lean_inc(x_447);
lean_inc_ref(x_446);
x_459 = l_Lean_Meta_matchConstructorApp_x3f(x_455, x_446, x_447, x_448, x_449);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
lean_dec_ref(x_459);
if (lean_obj_tag(x_460) == 1)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_461 = lean_ctor_get(x_458, 0);
lean_inc_ref(x_461);
lean_dec(x_458);
x_462 = lean_ctor_get(x_460, 0);
lean_inc(x_462);
lean_dec_ref(x_460);
x_463 = lean_ctor_get(x_462, 0);
lean_inc_ref(x_463);
lean_dec(x_462);
x_464 = lean_ctor_get(x_461, 0);
lean_inc(x_464);
lean_dec_ref(x_461);
x_465 = lean_ctor_get(x_463, 0);
lean_inc(x_465);
lean_dec_ref(x_463);
x_466 = lean_name_eq(x_464, x_465);
lean_dec(x_465);
lean_dec(x_464);
if (x_466 == 0)
{
lean_dec_ref(x_151);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_36 = x_449;
x_37 = x_448;
x_38 = x_447;
x_39 = x_446;
goto block_76;
}
else
{
if (x_106 == 0)
{
lean_del_object(x_33);
x_396 = x_12;
x_397 = x_446;
x_398 = x_447;
x_399 = x_448;
x_400 = x_449;
goto block_445;
}
else
{
lean_dec_ref(x_151);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_36 = x_449;
x_37 = x_448;
x_38 = x_447;
x_39 = x_446;
goto block_76;
}
}
}
else
{
lean_dec(x_460);
lean_dec(x_458);
lean_del_object(x_33);
x_396 = x_12;
x_397 = x_446;
x_398 = x_447;
x_399 = x_448;
x_400 = x_449;
goto block_445;
}
}
else
{
lean_object* x_467; lean_object* x_468; uint8_t x_469; uint8_t x_474; 
lean_dec(x_458);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_467 = lean_ctor_get(x_459, 0);
x_474 = !lean_is_exclusive(x_459);
if (x_474 == 0)
{
x_468 = x_459;
x_469 = x_474;
goto block_473;
}
else
{
lean_inc(x_467);
lean_dec(x_459);
x_468 = lean_box(0);
x_469 = x_474;
goto block_473;
}
block_473:
{
lean_object* x_470; 
if (x_469 == 0)
{
x_470 = x_468;
goto block_471;
}
else
{
lean_object* x_472; 
x_472 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_472, 0, x_467);
x_470 = x_472;
goto block_471;
}
block_471:
{
return x_470;
}
}
}
}
else
{
lean_dec(x_457);
lean_dec(x_455);
lean_del_object(x_33);
x_396 = x_12;
x_397 = x_446;
x_398 = x_447;
x_399 = x_448;
x_400 = x_449;
goto block_445;
}
}
else
{
lean_object* x_475; lean_object* x_476; uint8_t x_477; uint8_t x_482; 
lean_dec(x_455);
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_475 = lean_ctor_get(x_456, 0);
x_482 = !lean_is_exclusive(x_456);
if (x_482 == 0)
{
x_476 = x_456;
x_477 = x_482;
goto block_481;
}
else
{
lean_inc(x_475);
lean_dec(x_456);
x_476 = lean_box(0);
x_477 = x_482;
goto block_481;
}
block_481:
{
lean_object* x_478; 
if (x_477 == 0)
{
x_478 = x_476;
goto block_479;
}
else
{
lean_object* x_480; 
x_480 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_480, 0, x_475);
x_478 = x_480;
goto block_479;
}
block_479:
{
return x_478;
}
}
}
}
else
{
lean_dec(x_451);
lean_del_object(x_33);
x_396 = x_106;
x_397 = x_446;
x_398 = x_447;
x_399 = x_448;
x_400 = x_449;
goto block_445;
}
}
else
{
lean_object* x_483; lean_object* x_484; uint8_t x_485; uint8_t x_490; 
lean_dec(x_449);
lean_dec_ref(x_448);
lean_dec(x_447);
lean_dec_ref(x_446);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_483 = lean_ctor_get(x_450, 0);
x_490 = !lean_is_exclusive(x_450);
if (x_490 == 0)
{
x_484 = x_450;
x_485 = x_490;
goto block_489;
}
else
{
lean_inc(x_483);
lean_dec(x_450);
x_484 = lean_box(0);
x_485 = x_490;
goto block_489;
}
block_489:
{
lean_object* x_486; 
if (x_485 == 0)
{
x_486 = x_484;
goto block_487;
}
else
{
lean_object* x_488; 
x_488 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_488, 0, x_483);
x_486 = x_488;
goto block_487;
}
block_487:
{
return x_486;
}
}
}
}
block_628:
{
lean_object* x_496; 
lean_inc(x_495);
lean_inc_ref(x_494);
lean_inc(x_493);
lean_inc_ref(x_492);
lean_inc_ref(x_151);
x_496 = l_refutableHasNotBit_x3f(x_151, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
lean_dec_ref(x_496);
if (lean_obj_tag(x_497) == 1)
{
lean_object* x_498; lean_object* x_499; uint8_t x_500; uint8_t x_538; 
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_498 = lean_ctor_get(x_497, 0);
x_538 = !lean_is_exclusive(x_497);
if (x_538 == 0)
{
x_499 = x_497;
x_500 = x_538;
goto block_537;
}
else
{
lean_inc(x_498);
lean_dec(x_497);
x_499 = lean_box(0);
x_500 = x_538;
goto block_537;
}
block_537:
{
lean_object* x_501; 
lean_inc(x_2);
x_501 = l_Lean_MVarId_getType(x_2, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
lean_dec_ref(x_501);
x_503 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_493);
x_504 = l_Lean_Meta_mkAbsurd(x_502, x_498, x_503, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
lean_dec_ref(x_504);
x_506 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_505, x_493);
lean_dec(x_493);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; 
lean_dec_ref(x_506);
x_507 = lean_box(x_12);
if (x_500 == 0)
{
lean_ctor_set(x_499, 0, x_507);
x_508 = x_499;
goto block_511;
}
else
{
lean_object* x_512; 
x_512 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_512, 0, x_507);
x_508 = x_512;
goto block_511;
}
block_511:
{
lean_object* x_509; lean_object* x_510; 
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_35);
x_510 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_510, 0, x_509);
x_17 = x_510;
goto block_23;
}
}
else
{
lean_object* x_513; lean_object* x_514; uint8_t x_515; uint8_t x_520; 
lean_del_object(x_499);
lean_del_object(x_15);
lean_dec(x_14);
x_513 = lean_ctor_get(x_506, 0);
x_520 = !lean_is_exclusive(x_506);
if (x_520 == 0)
{
x_514 = x_506;
x_515 = x_520;
goto block_519;
}
else
{
lean_inc(x_513);
lean_dec(x_506);
x_514 = lean_box(0);
x_515 = x_520;
goto block_519;
}
block_519:
{
lean_object* x_516; 
if (x_515 == 0)
{
x_516 = x_514;
goto block_517;
}
else
{
lean_object* x_518; 
x_518 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_518, 0, x_513);
x_516 = x_518;
goto block_517;
}
block_517:
{
return x_516;
}
}
}
}
else
{
lean_object* x_521; lean_object* x_522; uint8_t x_523; uint8_t x_528; 
lean_del_object(x_499);
lean_dec(x_493);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_521 = lean_ctor_get(x_504, 0);
x_528 = !lean_is_exclusive(x_504);
if (x_528 == 0)
{
x_522 = x_504;
x_523 = x_528;
goto block_527;
}
else
{
lean_inc(x_521);
lean_dec(x_504);
x_522 = lean_box(0);
x_523 = x_528;
goto block_527;
}
block_527:
{
lean_object* x_524; 
if (x_523 == 0)
{
x_524 = x_522;
goto block_525;
}
else
{
lean_object* x_526; 
x_526 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_526, 0, x_521);
x_524 = x_526;
goto block_525;
}
block_525:
{
return x_524;
}
}
}
}
else
{
lean_object* x_529; lean_object* x_530; uint8_t x_531; uint8_t x_536; 
lean_del_object(x_499);
lean_dec(x_498);
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_529 = lean_ctor_get(x_501, 0);
x_536 = !lean_is_exclusive(x_501);
if (x_536 == 0)
{
x_530 = x_501;
x_531 = x_536;
goto block_535;
}
else
{
lean_inc(x_529);
lean_dec(x_501);
x_530 = lean_box(0);
x_531 = x_536;
goto block_535;
}
block_535:
{
lean_object* x_532; 
if (x_531 == 0)
{
x_532 = x_530;
goto block_533;
}
else
{
lean_object* x_534; 
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_529);
x_532 = x_534;
goto block_533;
}
block_533:
{
return x_532;
}
}
}
}
}
else
{
lean_object* x_539; 
lean_dec(x_497);
lean_inc(x_495);
lean_inc_ref(x_494);
lean_inc(x_493);
lean_inc_ref(x_492);
lean_inc_ref(x_151);
x_539 = l_Lean_Meta_matchNe_x3f(x_151, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
lean_dec_ref(x_539);
if (lean_obj_tag(x_540) == 1)
{
lean_object* x_541; lean_object* x_542; uint8_t x_543; uint8_t x_611; 
x_541 = lean_ctor_get(x_540, 0);
x_611 = !lean_is_exclusive(x_540);
if (x_611 == 0)
{
x_542 = x_540;
x_543 = x_611;
goto block_610;
}
else
{
lean_inc(x_541);
lean_dec(x_540);
x_542 = lean_box(0);
x_543 = x_611;
goto block_610;
}
block_610:
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; uint8_t x_609; 
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
lean_dec(x_541);
x_545 = lean_ctor_get(x_544, 0);
x_546 = lean_ctor_get(x_544, 1);
x_609 = !lean_is_exclusive(x_544);
if (x_609 == 0)
{
x_547 = x_544;
x_548 = x_609;
goto block_608;
}
else
{
lean_inc(x_546);
lean_inc(x_545);
lean_dec(x_544);
x_547 = lean_box(0);
x_548 = x_609;
goto block_608;
}
block_608:
{
lean_object* x_549; 
lean_inc(x_495);
lean_inc_ref(x_494);
lean_inc(x_493);
lean_inc_ref(x_492);
lean_inc(x_545);
x_549 = l_Lean_Meta_isExprDefEq(x_545, x_546, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; uint8_t x_551; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
lean_dec_ref(x_549);
x_551 = lean_unbox(x_550);
lean_dec(x_550);
if (x_551 == 0)
{
lean_del_object(x_547);
lean_dec(x_545);
lean_del_object(x_542);
x_446 = x_492;
x_447 = x_493;
x_448 = x_494;
x_449 = x_495;
goto block_491;
}
else
{
lean_object* x_552; 
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_1);
lean_inc(x_2);
x_552 = l_Lean_MVarId_getType(x_2, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
lean_dec_ref(x_552);
lean_inc(x_495);
lean_inc_ref(x_494);
lean_inc(x_493);
lean_inc_ref(x_492);
x_554 = l_Lean_Meta_mkEqRefl(x_545, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_554, 0);
lean_inc(x_555);
lean_dec_ref(x_554);
x_556 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_493);
x_557 = l_Lean_Meta_mkAbsurd(x_553, x_555, x_556, x_492, x_493, x_494, x_495);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
lean_dec_ref(x_557);
x_559 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_558, x_493);
lean_dec(x_493);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; 
lean_dec_ref(x_559);
x_560 = lean_box(x_12);
if (x_543 == 0)
{
lean_ctor_set(x_542, 0, x_560);
x_561 = x_542;
goto block_566;
}
else
{
lean_object* x_567; 
x_567 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_567, 0, x_560);
x_561 = x_567;
goto block_566;
}
block_566:
{
lean_object* x_562; 
if (x_548 == 0)
{
lean_ctor_set(x_547, 1, x_35);
lean_ctor_set(x_547, 0, x_561);
x_562 = x_547;
goto block_564;
}
else
{
lean_object* x_565; 
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_561);
lean_ctor_set(x_565, 1, x_35);
x_562 = x_565;
goto block_564;
}
block_564:
{
lean_object* x_563; 
x_563 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_563, 0, x_562);
x_17 = x_563;
goto block_23;
}
}
}
else
{
lean_object* x_568; lean_object* x_569; uint8_t x_570; uint8_t x_575; 
lean_del_object(x_547);
lean_del_object(x_542);
lean_del_object(x_15);
lean_dec(x_14);
x_568 = lean_ctor_get(x_559, 0);
x_575 = !lean_is_exclusive(x_559);
if (x_575 == 0)
{
x_569 = x_559;
x_570 = x_575;
goto block_574;
}
else
{
lean_inc(x_568);
lean_dec(x_559);
x_569 = lean_box(0);
x_570 = x_575;
goto block_574;
}
block_574:
{
lean_object* x_571; 
if (x_570 == 0)
{
x_571 = x_569;
goto block_572;
}
else
{
lean_object* x_573; 
x_573 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_573, 0, x_568);
x_571 = x_573;
goto block_572;
}
block_572:
{
return x_571;
}
}
}
}
else
{
lean_object* x_576; lean_object* x_577; uint8_t x_578; uint8_t x_583; 
lean_del_object(x_547);
lean_del_object(x_542);
lean_dec(x_493);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_576 = lean_ctor_get(x_557, 0);
x_583 = !lean_is_exclusive(x_557);
if (x_583 == 0)
{
x_577 = x_557;
x_578 = x_583;
goto block_582;
}
else
{
lean_inc(x_576);
lean_dec(x_557);
x_577 = lean_box(0);
x_578 = x_583;
goto block_582;
}
block_582:
{
lean_object* x_579; 
if (x_578 == 0)
{
x_579 = x_577;
goto block_580;
}
else
{
lean_object* x_581; 
x_581 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_581, 0, x_576);
x_579 = x_581;
goto block_580;
}
block_580:
{
return x_579;
}
}
}
}
else
{
lean_object* x_584; lean_object* x_585; uint8_t x_586; uint8_t x_591; 
lean_dec(x_553);
lean_del_object(x_547);
lean_del_object(x_542);
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_584 = lean_ctor_get(x_554, 0);
x_591 = !lean_is_exclusive(x_554);
if (x_591 == 0)
{
x_585 = x_554;
x_586 = x_591;
goto block_590;
}
else
{
lean_inc(x_584);
lean_dec(x_554);
x_585 = lean_box(0);
x_586 = x_591;
goto block_590;
}
block_590:
{
lean_object* x_587; 
if (x_586 == 0)
{
x_587 = x_585;
goto block_588;
}
else
{
lean_object* x_589; 
x_589 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_589, 0, x_584);
x_587 = x_589;
goto block_588;
}
block_588:
{
return x_587;
}
}
}
}
else
{
lean_object* x_592; lean_object* x_593; uint8_t x_594; uint8_t x_599; 
lean_del_object(x_547);
lean_dec(x_545);
lean_del_object(x_542);
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_592 = lean_ctor_get(x_552, 0);
x_599 = !lean_is_exclusive(x_552);
if (x_599 == 0)
{
x_593 = x_552;
x_594 = x_599;
goto block_598;
}
else
{
lean_inc(x_592);
lean_dec(x_552);
x_593 = lean_box(0);
x_594 = x_599;
goto block_598;
}
block_598:
{
lean_object* x_595; 
if (x_594 == 0)
{
x_595 = x_593;
goto block_596;
}
else
{
lean_object* x_597; 
x_597 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_597, 0, x_592);
x_595 = x_597;
goto block_596;
}
block_596:
{
return x_595;
}
}
}
}
}
else
{
lean_object* x_600; lean_object* x_601; uint8_t x_602; uint8_t x_607; 
lean_del_object(x_547);
lean_dec(x_545);
lean_del_object(x_542);
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_600 = lean_ctor_get(x_549, 0);
x_607 = !lean_is_exclusive(x_549);
if (x_607 == 0)
{
x_601 = x_549;
x_602 = x_607;
goto block_606;
}
else
{
lean_inc(x_600);
lean_dec(x_549);
x_601 = lean_box(0);
x_602 = x_607;
goto block_606;
}
block_606:
{
lean_object* x_603; 
if (x_602 == 0)
{
x_603 = x_601;
goto block_604;
}
else
{
lean_object* x_605; 
x_605 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_605, 0, x_600);
x_603 = x_605;
goto block_604;
}
block_604:
{
return x_603;
}
}
}
}
}
}
else
{
lean_dec(x_540);
x_446 = x_492;
x_447 = x_493;
x_448 = x_494;
x_449 = x_495;
goto block_491;
}
}
else
{
lean_object* x_612; lean_object* x_613; uint8_t x_614; uint8_t x_619; 
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_612 = lean_ctor_get(x_539, 0);
x_619 = !lean_is_exclusive(x_539);
if (x_619 == 0)
{
x_613 = x_539;
x_614 = x_619;
goto block_618;
}
else
{
lean_inc(x_612);
lean_dec(x_539);
x_613 = lean_box(0);
x_614 = x_619;
goto block_618;
}
block_618:
{
lean_object* x_615; 
if (x_614 == 0)
{
x_615 = x_613;
goto block_616;
}
else
{
lean_object* x_617; 
x_617 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_617, 0, x_612);
x_615 = x_617;
goto block_616;
}
block_616:
{
return x_615;
}
}
}
}
}
else
{
lean_object* x_620; lean_object* x_621; uint8_t x_622; uint8_t x_627; 
lean_dec(x_495);
lean_dec_ref(x_494);
lean_dec(x_493);
lean_dec_ref(x_492);
lean_dec_ref(x_151);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_620 = lean_ctor_get(x_496, 0);
x_627 = !lean_is_exclusive(x_496);
if (x_627 == 0)
{
x_621 = x_496;
x_622 = x_627;
goto block_626;
}
else
{
lean_inc(x_620);
lean_dec(x_496);
x_621 = lean_box(0);
x_622 = x_627;
goto block_626;
}
block_626:
{
lean_object* x_623; 
if (x_622 == 0)
{
x_623 = x_621;
goto block_624;
}
else
{
lean_object* x_625; 
x_625 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_625, 0, x_620);
x_623 = x_625;
goto block_624;
}
block_624:
{
return x_623;
}
}
}
}
}
else
{
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_77;
goto block_30;
}
block_76:
{
lean_object* x_40; 
lean_inc(x_2);
x_40 = l_Lean_MVarId_getType(x_2, x_39, x_38, x_37, x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_LocalDecl_toExpr(x_32);
lean_inc(x_38);
x_43 = l_Lean_Meta_mkNoConfusion(x_41, x_42, x_39, x_38, x_37, x_36);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(x_2, x_44, x_38);
lean_dec(x_38);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec_ref(x_45);
x_46 = lean_box(x_12);
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_46);
x_47 = x_33;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_47 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_17 = x_49;
goto block_23;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_del_object(x_33);
lean_del_object(x_15);
lean_dec(x_14);
x_52 = lean_ctor_get(x_45, 0);
x_59 = !lean_is_exclusive(x_45);
if (x_59 == 0)
{
x_53 = x_45;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_67; 
lean_dec(x_38);
lean_del_object(x_33);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_60 = lean_ctor_get(x_43, 0);
x_67 = !lean_is_exclusive(x_43);
if (x_67 == 0)
{
x_61 = x_43;
x_62 = x_67;
goto block_66;
}
else
{
lean_inc(x_60);
lean_dec(x_43);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_37);
lean_dec(x_36);
lean_del_object(x_33);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_68 = lean_ctor_get(x_40, 0);
x_75 = !lean_is_exclusive(x_40);
if (x_75 == 0)
{
x_69 = x_40;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_40);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
block_99:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_1, 0);
x_83 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
lean_inc(x_82);
lean_inc(x_2);
x_84 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(x_2, x_83, x_82, x_80, x_79, x_78, x_81);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_77;
goto block_30;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_87 = lean_box(x_12);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_35);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_17 = x_90;
goto block_23;
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_98; 
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_91 = lean_ctor_get(x_84, 0);
x_98 = !lean_is_exclusive(x_84);
if (x_98 == 0)
{
x_92 = x_84;
x_93 = x_98;
goto block_97;
}
else
{
lean_inc(x_91);
lean_dec(x_84);
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
block_105:
{
if (x_104 == 0)
{
lean_dec(x_103);
lean_dec_ref(x_102);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
x_25 = x_77;
goto block_30;
}
else
{
x_78 = x_101;
x_79 = x_100;
x_80 = x_102;
x_81 = x_103;
goto block_99;
}
}
block_112:
{
if (x_109 == 0)
{
x_78 = x_108;
x_79 = x_107;
x_80 = x_110;
x_81 = x_111;
goto block_99;
}
else
{
x_100 = x_107;
x_101 = x_108;
x_102 = x_110;
x_103 = x_111;
x_104 = x_106;
goto block_105;
}
}
block_119:
{
if (x_118 == 0)
{
x_100 = x_114;
x_101 = x_113;
x_102 = x_116;
x_103 = x_117;
x_104 = x_106;
goto block_105;
}
else
{
x_107 = x_114;
x_108 = x_113;
x_109 = x_115;
x_110 = x_116;
x_111 = x_117;
goto block_112;
}
}
block_127:
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_126 == 0)
{
x_113 = x_124;
x_114 = x_123;
x_115 = x_121;
x_116 = x_122;
x_117 = x_125;
x_118 = x_106;
goto block_119;
}
else
{
if (x_120 == 0)
{
x_107 = x_123;
x_108 = x_124;
x_109 = x_121;
x_110 = x_122;
x_111 = x_125;
goto block_112;
}
else
{
x_113 = x_124;
x_114 = x_123;
x_115 = x_121;
x_116 = x_122;
x_117 = x_125;
x_118 = x_106;
goto block_119;
}
}
}
block_150:
{
if (x_134 == 0)
{
x_120 = x_128;
x_121 = x_129;
x_122 = x_132;
x_123 = x_130;
x_124 = x_131;
x_125 = x_133;
goto block_127;
}
else
{
lean_object* x_135; 
lean_inc(x_133);
lean_inc_ref(x_131);
lean_inc(x_130);
lean_inc_ref(x_132);
lean_inc(x_32);
lean_inc(x_2);
x_135 = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(x_2, x_32, x_132, x_130, x_131, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = lean_unbox(x_136);
lean_dec(x_136);
if (x_137 == 0)
{
x_120 = x_128;
x_121 = x_129;
x_122 = x_132;
x_123 = x_130;
x_124 = x_131;
x_125 = x_133;
goto block_127;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_32);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_138 = lean_box(x_12);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_35);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_17 = x_141;
goto block_23;
}
}
else
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; uint8_t x_149; 
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec(x_130);
lean_dec(x_32);
lean_del_object(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
x_142 = lean_ctor_get(x_135, 0);
x_149 = !lean_is_exclusive(x_135);
if (x_149 == 0)
{
x_143 = x_135;
x_144 = x_149;
goto block_148;
}
else
{
lean_inc(x_142);
lean_dec(x_135);
x_143 = lean_box(0);
x_144 = x_149;
goto block_148;
}
block_148:
{
lean_object* x_145; 
if (x_144 == 0)
{
x_145 = x_143;
goto block_146;
}
else
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_142);
x_145 = x_147;
goto block_146;
}
block_146:
{
return x_145;
}
}
}
}
}
}
}
block_23:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_18);
x_19 = x_15;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_14);
x_19 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
block_30:
{
lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_5, x_27);
x_29 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(x_1, x_2, x_3, x_4, x_28, x_26, x_7, x_8, x_9, x_10);
return x_29;
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
