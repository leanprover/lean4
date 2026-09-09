// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Goal
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.Tactic.Util import Lean.Meta.Sym.InferType
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
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_noProgress_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_noProgress_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_closed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_closed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_goal_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_goal_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "`Sym.simp` made no progress "};
static const lean_object* l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_toOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_toOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mpr"};
static const lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__1_value),LEAN_SCALAR_PTR_LITERAL(146, 109, 21, 40, 70, 113, 251, 6)}};
static const lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__3_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_ctor_object l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__4_value),LEAN_SCALAR_PTR_LITERAL(177, 152, 123, 219, 220, 182, 189, 250)}};
static const lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalIgnoringNoProgress(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalIgnoringNoProgress___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Meta_Sym_SimpGoalResult_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 2)
{
lean_object* v_mvarId_9_; lean_object* v___x_10_; 
v_mvarId_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_mvarId_9_);
lean_dec_ref_known(v_t_7_, 1);
v___x_10_ = lean_apply_1(v_k_8_, v_mvarId_9_);
return v___x_10_;
}
else
{
lean_dec(v_t_7_);
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_noProgress_elim___redArg(lean_object* v_t_23_, lean_object* v_noProgress_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_23_, v_noProgress_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_noProgress_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_noProgress_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_27_, v_noProgress_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_closed_elim___redArg(lean_object* v_t_31_, lean_object* v_closed_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_31_, v_closed_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_closed_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_closed_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_35_, v_closed_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_goal_elim___redArg(lean_object* v_t_39_, lean_object* v_goal_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_39_, v_goal_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_goal_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_goal_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_43_, v_goal_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_47_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1);
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
lean_ctor_set(v___x_52_, 2, v___x_51_);
lean_ctor_set(v___x_52_, 3, v___x_51_);
lean_ctor_set(v___x_52_, 4, v___x_50_);
lean_ctor_set(v___x_52_, 5, v___x_50_);
lean_ctor_set(v___x_52_, 6, v___x_50_);
lean_ctor_set(v___x_52_, 7, v___x_50_);
lean_ctor_set(v___x_52_, 8, v___x_50_);
lean_ctor_set(v___x_52_, 9, v___x_50_);
lean_ctor_set(v___x_52_, 10, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_unsigned_to_nat(32u);
v___x_54_ = lean_mk_empty_array_with_capacity(v___x_53_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_56_ = ((size_t)5ULL);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_unsigned_to_nat(32u);
v___x_59_ = lean_mk_empty_array_with_capacity(v___x_58_);
v___x_60_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3);
v___x_61_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
lean_ctor_set(v___x_61_, 2, v___x_57_);
lean_ctor_set(v___x_61_, 3, v___x_57_);
lean_ctor_set_usize(v___x_61_, 4, v___x_56_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = lean_box(1);
v___x_63_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4);
v___x_64_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1);
v___x_65_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
lean_ctor_set(v___x_65_, 2, v___x_62_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(lean_object* v_msgData_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; lean_object* v_toCold_71_; lean_object* v_env_72_; lean_object* v_options_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_70_ = lean_st_ref_get(v___y_68_);
v_toCold_71_ = lean_ctor_get(v___y_67_, 0);
v_env_72_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_env_72_);
lean_dec(v___x_70_);
v_options_73_ = lean_ctor_get(v_toCold_71_, 2);
v___x_74_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2);
v___x_75_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_73_);
v___x_76_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_76_, 0, v_env_72_);
lean_ctor_set(v___x_76_, 1, v___x_74_);
lean_ctor_set(v___x_76_, 2, v___x_75_);
lean_ctor_set(v___x_76_, 3, v_options_73_);
v___x_77_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v_msgData_66_);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___boxed(lean_object* v_msgData_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(v_msgData_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(lean_object* v_msg_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v_ref_88_; lean_object* v___x_89_; lean_object* v_a_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_98_; 
v_ref_88_ = lean_ctor_get(v___y_85_, 2);
v___x_89_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(v_msg_84_, v___y_85_, v___y_86_);
v_a_90_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_98_ == 0)
{
v___x_92_ = v___x_89_;
v_isShared_93_ = v_isSharedCheck_98_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_a_90_);
lean_dec(v___x_89_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_98_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; lean_object* v___x_96_; 
lean_inc(v_ref_88_);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_ref_88_);
lean_ctor_set(v___x_94_, 1, v_a_90_);
if (v_isShared_93_ == 0)
{
lean_ctor_set_tag(v___x_92_, 1);
lean_ctor_set(v___x_92_, 0, v___x_94_);
v___x_96_ = v___x_92_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg___boxed(lean_object* v_msg_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(v_msg_99_, v___y_100_, v___y_101_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_103_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__0));
v___x_106_ = l_Lean_stringToMessageData(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_toOption(lean_object* v_x_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
switch(lean_obj_tag(v_x_107_))
{
case 0:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1, &l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1_once, _init_l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1);
v___x_112_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(v___x_111_, v_a_108_, v_a_109_);
return v___x_112_;
}
case 1:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_box(0);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
default: 
{
lean_object* v_mvarId_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_123_; 
v_mvarId_115_ = lean_ctor_get(v_x_107_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_107_);
if (v_isSharedCheck_123_ == 0)
{
v___x_117_ = v_x_107_;
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_mvarId_115_);
lean_dec(v_x_107_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set_tag(v___x_117_, 1);
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_mvarId_115_);
v___x_120_ = v_reuseFailAlloc_122_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_121_; 
v___x_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
return v___x_121_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_toOption___boxed(lean_object* v_x_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_Meta_Sym_SimpGoalResult_toOption(v_x_124_, v_a_125_, v_a_126_);
lean_dec(v_a_126_);
lean_dec_ref(v_a_125_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0(lean_object* v_00_u03b1_129_, lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(v_msg_130_, v___y_131_, v___y_132_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___boxed(lean_object* v_00_u03b1_135_, lean_object* v_msg_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0(v_00_u03b1_135_, v_msg_136_, v___y_137_, v___y_138_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress(lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
if (lean_obj_tag(v_x_141_) == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_143_, 0, v_x_142_);
return v___x_143_;
}
else
{
lean_dec(v_x_142_);
lean_inc(v_x_141_);
return v_x_141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress___boxed(lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress(v_x_144_, v_x_145_);
lean_dec(v_x_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_ks_151_; lean_object* v_vs_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_176_; 
v_ks_151_ = lean_ctor_get(v_x_147_, 0);
v_vs_152_ = lean_ctor_get(v_x_147_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_176_ == 0)
{
v___x_154_ = v_x_147_;
v_isShared_155_ = v_isSharedCheck_176_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_vs_152_);
lean_inc(v_ks_151_);
lean_dec(v_x_147_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_176_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_array_get_size(v_ks_151_);
v___x_157_ = lean_nat_dec_lt(v_x_148_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_161_; 
lean_dec(v_x_148_);
v___x_158_ = lean_array_push(v_ks_151_, v_x_149_);
v___x_159_ = lean_array_push(v_vs_152_, v_x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___x_159_);
lean_ctor_set(v___x_154_, 0, v___x_158_);
v___x_161_ = v___x_154_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
else
{
lean_object* v_k_x27_163_; uint8_t v___x_164_; 
v_k_x27_163_ = lean_array_fget_borrowed(v_ks_151_, v_x_148_);
v___x_164_ = l_Lean_instBEqMVarId_beq(v_x_149_, v_k_x27_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_166_; 
if (v_isShared_155_ == 0)
{
v___x_166_ = v___x_154_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_ks_151_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_vs_152_);
v___x_166_ = v_reuseFailAlloc_170_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_add(v_x_148_, v___x_167_);
lean_dec(v_x_148_);
v_x_147_ = v___x_166_;
v_x_148_ = v___x_168_;
goto _start;
}
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_171_ = lean_array_fset(v_ks_151_, v_x_148_, v_x_149_);
v___x_172_ = lean_array_fset(v_vs_152_, v_x_148_, v_x_150_);
lean_dec(v_x_148_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___x_172_);
lean_ctor_set(v___x_154_, 0, v___x_171_);
v___x_174_ = v___x_154_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_177_, lean_object* v_k_178_, lean_object* v_v_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_177_, v___x_180_, v_k_178_, v_v_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(lean_object* v_x_183_, size_t v_x_184_, size_t v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v_es_188_; size_t v___x_189_; size_t v___x_190_; lean_object* v_j_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_es_188_ = lean_ctor_get(v_x_183_, 0);
v___x_189_ = ((size_t)31ULL);
v___x_190_ = lean_usize_land(v_x_184_, v___x_189_);
v_j_191_ = lean_usize_to_nat(v___x_190_);
v___x_192_ = lean_array_get_size(v_es_188_);
v___x_193_ = lean_nat_dec_lt(v_j_191_, v___x_192_);
if (v___x_193_ == 0)
{
lean_dec(v_j_191_);
lean_dec(v_x_187_);
lean_dec(v_x_186_);
return v_x_183_;
}
else
{
lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_232_; 
lean_inc_ref(v_es_188_);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v_x_183_, 0);
lean_dec(v_unused_233_);
v___x_195_ = v_x_183_;
v_isShared_196_ = v_isSharedCheck_232_;
goto v_resetjp_194_;
}
else
{
lean_dec(v_x_183_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_232_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v_v_197_; lean_object* v___x_198_; lean_object* v_xs_x27_199_; lean_object* v___y_201_; 
v_v_197_ = lean_array_fget(v_es_188_, v_j_191_);
v___x_198_ = lean_box(0);
v_xs_x27_199_ = lean_array_fset(v_es_188_, v_j_191_, v___x_198_);
switch(lean_obj_tag(v_v_197_))
{
case 0:
{
lean_object* v_key_206_; lean_object* v_val_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_217_; 
v_key_206_ = lean_ctor_get(v_v_197_, 0);
v_val_207_ = lean_ctor_get(v_v_197_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_v_197_);
if (v_isSharedCheck_217_ == 0)
{
v___x_209_ = v_v_197_;
v_isShared_210_ = v_isSharedCheck_217_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_val_207_);
lean_inc(v_key_206_);
lean_dec(v_v_197_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_217_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
uint8_t v___x_211_; 
v___x_211_ = l_Lean_instBEqMVarId_beq(v_x_186_, v_key_206_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_del_object(v___x_209_);
v___x_212_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_206_, v_val_207_, v_x_186_, v_x_187_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___y_201_ = v___x_213_;
goto v___jp_200_;
}
else
{
lean_object* v___x_215_; 
lean_dec(v_val_207_);
lean_dec(v_key_206_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v_x_187_);
lean_ctor_set(v___x_209_, 0, v_x_186_);
v___x_215_ = v___x_209_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_x_186_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_x_187_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
v___y_201_ = v___x_215_;
goto v___jp_200_;
}
}
}
}
case 1:
{
lean_object* v_node_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_230_; 
v_node_218_ = lean_ctor_get(v_v_197_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v_v_197_);
if (v_isSharedCheck_230_ == 0)
{
v___x_220_ = v_v_197_;
v_isShared_221_ = v_isSharedCheck_230_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_node_218_);
lean_dec(v_v_197_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_230_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; size_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_222_ = ((size_t)5ULL);
v___x_223_ = lean_usize_shift_right(v_x_184_, v___x_222_);
v___x_224_ = ((size_t)1ULL);
v___x_225_ = lean_usize_add(v_x_185_, v___x_224_);
v___x_226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_node_218_, v___x_223_, v___x_225_, v_x_186_, v_x_187_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_226_);
v___x_228_ = v___x_220_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
v___y_201_ = v___x_228_;
goto v___jp_200_;
}
}
}
default: 
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_x_186_);
lean_ctor_set(v___x_231_, 1, v_x_187_);
v___y_201_ = v___x_231_;
goto v___jp_200_;
}
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_array_fset(v_xs_x27_199_, v_j_191_, v___y_201_);
lean_dec(v_j_191_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_202_);
v___x_204_ = v___x_195_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
else
{
lean_object* v_ks_234_; lean_object* v_vs_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_253_; 
v_ks_234_ = lean_ctor_get(v_x_183_, 0);
v_vs_235_ = lean_ctor_get(v_x_183_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_253_ == 0)
{
v___x_237_ = v_x_183_;
v_isShared_238_ = v_isSharedCheck_253_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_vs_235_);
lean_inc(v_ks_234_);
lean_dec(v_x_183_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_253_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_ks_234_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_vs_235_);
v___x_240_ = v_reuseFailAlloc_252_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v_newNode_241_; size_t v___x_242_; uint8_t v___x_243_; 
v_newNode_241_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(v___x_240_, v_x_186_, v_x_187_);
v___x_242_ = ((size_t)7ULL);
v___x_243_ = lean_usize_dec_le(v___x_242_, v_x_185_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_244_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_241_);
v___x_245_ = lean_unsigned_to_nat(4u);
v___x_246_ = lean_nat_dec_lt(v___x_244_, v___x_245_);
lean_dec(v___x_244_);
if (v___x_246_ == 0)
{
lean_object* v_ks_247_; lean_object* v_vs_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_ks_247_ = lean_ctor_get(v_newNode_241_, 0);
lean_inc_ref(v_ks_247_);
v_vs_248_ = lean_ctor_get(v_newNode_241_, 1);
lean_inc_ref(v_vs_248_);
lean_dec_ref(v_newNode_241_);
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_251_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_x_185_, v_ks_247_, v_vs_248_, v___x_249_, v___x_250_);
lean_dec_ref(v_vs_248_);
lean_dec_ref(v_ks_247_);
return v___x_251_;
}
else
{
return v_newNode_241_;
}
}
else
{
return v_newNode_241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_254_, lean_object* v_keys_255_, lean_object* v_vals_256_, lean_object* v_i_257_, lean_object* v_entries_258_){
_start:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_get_size(v_keys_255_);
v___x_260_ = lean_nat_dec_lt(v_i_257_, v___x_259_);
if (v___x_260_ == 0)
{
lean_dec(v_i_257_);
return v_entries_258_;
}
else
{
lean_object* v_k_261_; lean_object* v_v_262_; uint64_t v___x_263_; size_t v_h_264_; size_t v___x_265_; lean_object* v___x_266_; size_t v___x_267_; size_t v___x_268_; size_t v___x_269_; size_t v_h_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_k_261_ = lean_array_fget_borrowed(v_keys_255_, v_i_257_);
v_v_262_ = lean_array_fget_borrowed(v_vals_256_, v_i_257_);
v___x_263_ = l_Lean_instHashableMVarId_hash(v_k_261_);
v_h_264_ = lean_uint64_to_usize(v___x_263_);
v___x_265_ = ((size_t)5ULL);
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = ((size_t)1ULL);
v___x_268_ = lean_usize_sub(v_depth_254_, v___x_267_);
v___x_269_ = lean_usize_mul(v___x_265_, v___x_268_);
v_h_270_ = lean_usize_shift_right(v_h_264_, v___x_269_);
v___x_271_ = lean_nat_add(v_i_257_, v___x_266_);
lean_dec(v_i_257_);
lean_inc(v_v_262_);
lean_inc(v_k_261_);
v___x_272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_entries_258_, v_h_270_, v_depth_254_, v_k_261_, v_v_262_);
v_i_257_ = v___x_271_;
v_entries_258_ = v___x_272_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_274_, lean_object* v_keys_275_, lean_object* v_vals_276_, lean_object* v_i_277_, lean_object* v_entries_278_){
_start:
{
size_t v_depth_boxed_279_; lean_object* v_res_280_; 
v_depth_boxed_279_ = lean_unbox_usize(v_depth_274_);
lean_dec(v_depth_274_);
v_res_280_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_279_, v_keys_275_, v_vals_276_, v_i_277_, v_entries_278_);
lean_dec_ref(v_vals_276_);
lean_dec_ref(v_keys_275_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
size_t v_x_3117__boxed_286_; size_t v_x_3118__boxed_287_; lean_object* v_res_288_; 
v_x_3117__boxed_286_ = lean_unbox_usize(v_x_282_);
lean_dec(v_x_282_);
v_x_3118__boxed_287_ = lean_unbox_usize(v_x_283_);
lean_dec(v_x_283_);
v_res_288_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_281_, v_x_3117__boxed_286_, v_x_3118__boxed_287_, v_x_284_, v_x_285_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_){
_start:
{
uint64_t v___x_292_; size_t v___x_293_; size_t v___x_294_; lean_object* v___x_295_; 
v___x_292_ = l_Lean_instHashableMVarId_hash(v_x_290_);
v___x_293_ = lean_uint64_to_usize(v___x_292_);
v___x_294_ = ((size_t)1ULL);
v___x_295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_289_, v___x_293_, v___x_294_, v_x_290_, v_x_291_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(lean_object* v_mvarId_296_, lean_object* v_val_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; lean_object* v_mctx_301_; lean_object* v_cache_302_; lean_object* v_zetaDeltaFVarIds_303_; lean_object* v_postponed_304_; lean_object* v_diag_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_334_; 
v___x_300_ = lean_st_ref_take(v___y_298_);
v_mctx_301_ = lean_ctor_get(v___x_300_, 0);
v_cache_302_ = lean_ctor_get(v___x_300_, 1);
v_zetaDeltaFVarIds_303_ = lean_ctor_get(v___x_300_, 2);
v_postponed_304_ = lean_ctor_get(v___x_300_, 3);
v_diag_305_ = lean_ctor_get(v___x_300_, 4);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_334_ == 0)
{
v___x_307_ = v___x_300_;
v_isShared_308_ = v_isSharedCheck_334_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_diag_305_);
lean_inc(v_postponed_304_);
lean_inc(v_zetaDeltaFVarIds_303_);
lean_inc(v_cache_302_);
lean_inc(v_mctx_301_);
lean_dec(v___x_300_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_334_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v_depth_309_; lean_object* v_levelAssignDepth_310_; lean_object* v_lmvarCounter_311_; lean_object* v_mvarCounter_312_; lean_object* v_lDecls_313_; lean_object* v_decls_314_; lean_object* v_userNames_315_; lean_object* v_lAssignment_316_; lean_object* v_eAssignment_317_; lean_object* v_dAssignment_318_; lean_object* v_instanceTypedMVars_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_333_; 
v_depth_309_ = lean_ctor_get(v_mctx_301_, 0);
v_levelAssignDepth_310_ = lean_ctor_get(v_mctx_301_, 1);
v_lmvarCounter_311_ = lean_ctor_get(v_mctx_301_, 2);
v_mvarCounter_312_ = lean_ctor_get(v_mctx_301_, 3);
v_lDecls_313_ = lean_ctor_get(v_mctx_301_, 4);
v_decls_314_ = lean_ctor_get(v_mctx_301_, 5);
v_userNames_315_ = lean_ctor_get(v_mctx_301_, 6);
v_lAssignment_316_ = lean_ctor_get(v_mctx_301_, 7);
v_eAssignment_317_ = lean_ctor_get(v_mctx_301_, 8);
v_dAssignment_318_ = lean_ctor_get(v_mctx_301_, 9);
v_instanceTypedMVars_319_ = lean_ctor_get(v_mctx_301_, 10);
v_isSharedCheck_333_ = !lean_is_exclusive(v_mctx_301_);
if (v_isSharedCheck_333_ == 0)
{
v___x_321_ = v_mctx_301_;
v_isShared_322_ = v_isSharedCheck_333_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_instanceTypedMVars_319_);
lean_inc(v_dAssignment_318_);
lean_inc(v_eAssignment_317_);
lean_inc(v_lAssignment_316_);
lean_inc(v_userNames_315_);
lean_inc(v_decls_314_);
lean_inc(v_lDecls_313_);
lean_inc(v_mvarCounter_312_);
lean_inc(v_lmvarCounter_311_);
lean_inc(v_levelAssignDepth_310_);
lean_inc(v_depth_309_);
lean_dec(v_mctx_301_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_333_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_325_; 
v___x_323_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(v_eAssignment_317_, v_mvarId_296_, v_val_297_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 8, v___x_323_);
v___x_325_ = v___x_321_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_depth_309_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_levelAssignDepth_310_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_lmvarCounter_311_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v_mvarCounter_312_);
lean_ctor_set(v_reuseFailAlloc_332_, 4, v_lDecls_313_);
lean_ctor_set(v_reuseFailAlloc_332_, 5, v_decls_314_);
lean_ctor_set(v_reuseFailAlloc_332_, 6, v_userNames_315_);
lean_ctor_set(v_reuseFailAlloc_332_, 7, v_lAssignment_316_);
lean_ctor_set(v_reuseFailAlloc_332_, 8, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_332_, 9, v_dAssignment_318_);
lean_ctor_set(v_reuseFailAlloc_332_, 10, v_instanceTypedMVars_319_);
v___x_325_ = v_reuseFailAlloc_332_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_327_; 
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 0, v___x_325_);
v___x_327_ = v___x_307_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_cache_302_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_zetaDeltaFVarIds_303_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v_postponed_304_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v_diag_305_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_st_ref_put(v___y_298_, v___x_327_);
v___x_329_ = lean_box(0);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg___boxed(lean_object* v_mvarId_335_, lean_object* v_val_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_335_, v_val_336_, v___y_337_);
lean_dec(v___y_337_);
return v_res_339_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = lean_box(0);
v___x_351_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5));
v___x_352_ = l_Lean_mkConst(v___x_351_, v___x_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object* v_result_353_, lean_object* v_mvarId_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___x_362_; 
lean_inc(v_mvarId_354_);
v___x_362_ = l_Lean_MVarId_getDecl(v_mvarId_354_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_362_) == 0)
{
if (lean_obj_tag(v_result_353_) == 0)
{
lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
lean_dec_ref_known(v_result_353_, 0);
lean_dec(v_mvarId_354_);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_370_ == 0)
{
lean_object* v_unused_371_; 
v_unused_371_ = lean_ctor_get(v___x_362_, 0);
lean_dec(v_unused_371_);
v___x_364_ = v___x_362_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_dec(v___x_362_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = lean_box(0);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_a_372_; lean_object* v_e_x27_373_; lean_object* v_proof_374_; lean_object* v_userName_375_; lean_object* v_type_376_; lean_object* v___x_377_; 
v_a_372_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_362_, 1);
v_e_x27_373_ = lean_ctor_get(v_result_353_, 0);
lean_inc_ref_n(v_e_x27_373_, 2);
v_proof_374_ = lean_ctor_get(v_result_353_, 1);
lean_inc_ref(v_proof_374_);
lean_dec_ref_known(v_result_353_, 2);
v_userName_375_ = lean_ctor_get(v_a_372_, 0);
lean_inc(v_userName_375_);
v_type_376_ = lean_ctor_get(v_a_372_, 2);
lean_inc_ref(v_type_376_);
lean_dec(v_a_372_);
v___x_377_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_e_x27_373_, v_userName_375_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_379_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
lean_dec_ref_known(v___x_377_, 1);
lean_inc_ref(v_type_376_);
v___x_379_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_376_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_408_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
v___x_381_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2));
v___x_382_ = lean_box(0);
v___x_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_383_, 0, v_a_380_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = l_Lean_mkConst(v___x_381_, v___x_383_);
lean_inc(v_a_378_);
lean_inc_ref(v_e_x27_373_);
v___x_385_ = l_Lean_mkApp4(v___x_384_, v_type_376_, v_e_x27_373_, v_proof_374_, v_a_378_);
v___x_386_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_354_, v___x_385_, v_a_358_);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_386_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_386_, 0);
lean_dec(v_unused_409_);
v___x_388_ = v___x_386_;
v_isShared_389_ = v_isSharedCheck_408_;
goto v_resetjp_387_;
}
else
{
lean_dec(v___x_386_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_408_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
uint8_t v___x_390_; 
v___x_390_ = l_Lean_Expr_isTrue(v_e_x27_373_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = l_Lean_Expr_mvarId_x21(v_a_378_);
lean_dec(v_a_378_);
v___x_392_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 0, v___x_392_);
v___x_394_ = v___x_388_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
lean_del_object(v___x_388_);
v___x_396_ = l_Lean_Expr_mvarId_x21(v_a_378_);
lean_dec(v_a_378_);
v___x_397_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6, &l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6_once, _init_l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6);
v___x_398_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v___x_396_, v___x_397_, v_a_358_);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v___x_398_, 0);
lean_dec(v_unused_407_);
v___x_400_ = v___x_398_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_dec(v___x_398_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_402_ = lean_box(1);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_a_378_);
lean_dec_ref(v_type_376_);
lean_dec_ref(v_proof_374_);
lean_dec_ref(v_e_x27_373_);
lean_dec(v_mvarId_354_);
v_a_410_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_379_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_379_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v_type_376_);
lean_dec_ref(v_proof_374_);
lean_dec_ref(v_e_x27_373_);
lean_dec(v_mvarId_354_);
v_a_418_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_377_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_377_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
lean_dec(v_mvarId_354_);
lean_dec_ref(v_result_353_);
v_a_426_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_433_ == 0)
{
v___x_428_ = v___x_362_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_362_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_426_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___boxed(lean_object* v_result_434_, lean_object* v_mvarId_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_result_434_, v_mvarId_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0(lean_object* v_mvarId_444_, lean_object* v_val_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_444_, v_val_445_, v___y_449_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___boxed(lean_object* v_mvarId_454_, lean_object* v_val_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0(v_mvarId_454_, v_val_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0(lean_object* v_00_u03b2_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(v_x_465_, v_x_466_, v_x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_469_, lean_object* v_x_470_, size_t v_x_471_, size_t v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_470_, v_x_471_, v_x_472_, v_x_473_, v_x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_476_, lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
size_t v_x_3546__boxed_482_; size_t v_x_3547__boxed_483_; lean_object* v_res_484_; 
v_x_3546__boxed_482_ = lean_unbox_usize(v_x_478_);
lean_dec(v_x_478_);
v_x_3547__boxed_483_ = lean_unbox_usize(v_x_479_);
lean_dec(v_x_479_);
v_res_484_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1(v_00_u03b2_476_, v_x_477_, v_x_3546__boxed_482_, v_x_3547__boxed_483_, v_x_480_, v_x_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_485_, lean_object* v_n_486_, lean_object* v_k_487_, lean_object* v_v_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(v_n_486_, v_k_487_, v_v_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_490_, size_t v_depth_491_, lean_object* v_keys_492_, lean_object* v_vals_493_, lean_object* v_heq_494_, lean_object* v_i_495_, lean_object* v_entries_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_491_, v_keys_492_, v_vals_493_, v_i_495_, v_entries_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_498_, lean_object* v_depth_499_, lean_object* v_keys_500_, lean_object* v_vals_501_, lean_object* v_heq_502_, lean_object* v_i_503_, lean_object* v_entries_504_){
_start:
{
size_t v_depth_boxed_505_; lean_object* v_res_506_; 
v_depth_boxed_505_ = lean_unbox_usize(v_depth_499_);
lean_dec(v_depth_499_);
v_res_506_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_498_, v_depth_boxed_505_, v_keys_500_, v_vals_501_, v_heq_502_, v_i_503_, v_entries_504_);
lean_dec_ref(v_vals_501_);
lean_dec_ref(v_keys_500_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_507_, lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_508_, v_x_509_, v_x_510_, v_x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0(lean_object* v_x_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; 
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
v___x_521_ = lean_apply_7(v_x_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, lean_box(0));
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0___boxed(lean_object* v_x_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0(v_x_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(lean_object* v_mvarId_531_, lean_object* v_x_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___f_540_; lean_object* v___x_541_; 
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_540_, 0, v_x_532_);
lean_closure_set(v___f_540_, 1, v___y_533_);
lean_closure_set(v___f_540_, 2, v___y_534_);
v___x_541_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_531_, v___f_540_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_541_) == 0)
{
return v___x_541_;
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_541_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_541_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___boxed(lean_object* v_mvarId_550_, lean_object* v_x_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_550_, v_x_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0(lean_object* v_00_u03b1_560_, lean_object* v_mvarId_561_, lean_object* v_x_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_561_, v_x_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___boxed(lean_object* v_00_u03b1_571_, lean_object* v_mvarId_572_, lean_object* v_x_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0(v_00_u03b1_571_, v_mvarId_572_, v_x_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___lam__0(lean_object* v_mvarId_582_, lean_object* v_methods_583_, lean_object* v_config_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; 
lean_inc(v_mvarId_582_);
v___x_592_ = l_Lean_MVarId_getDecl(v_mvarId_582_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v_type_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref_known(v___x_592_, 1);
v_type_594_ = lean_ctor_get(v_a_593_, 2);
lean_inc_ref(v_type_594_);
lean_dec(v_a_593_);
v___x_595_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_595_, 0, v_type_594_);
v___x_596_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_595_, v_methods_583_, v_config_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_598_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_a_597_, v_mvarId_582_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_);
return v___x_598_;
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_mvarId_582_);
v_a_599_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_596_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_596_);
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
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_config_584_);
lean_dec_ref(v_methods_583_);
lean_dec(v_mvarId_582_);
v_a_607_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_592_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_592_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___lam__0___boxed(lean_object* v_mvarId_615_, lean_object* v_methods_616_, lean_object* v_config_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Meta_Sym_simpGoal___lam__0(v_mvarId_615_, v_methods_616_, v_config_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal(lean_object* v_mvarId_626_, lean_object* v_methods_627_, lean_object* v_config_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___f_636_; lean_object* v___x_637_; 
lean_inc(v_mvarId_626_);
v___f_636_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_simpGoal___lam__0___boxed), 10, 3);
lean_closure_set(v___f_636_, 0, v_mvarId_626_);
lean_closure_set(v___f_636_, 1, v_methods_627_);
lean_closure_set(v___f_636_, 2, v_config_628_);
v___x_637_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_626_, v___f_636_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___boxed(lean_object* v_mvarId_638_, lean_object* v_methods_639_, lean_object* v_config_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_638_, v_methods_639_, v_config_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalIgnoringNoProgress(lean_object* v_mvarId_649_, lean_object* v_methods_650_, lean_object* v_config_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
lean_object* v___x_659_; 
lean_inc(v_mvarId_649_);
v___x_659_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_649_, v_methods_650_, v_config_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
if (lean_obj_tag(v___x_659_) == 0)
{
lean_object* v_a_660_; 
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
if (lean_obj_tag(v_a_660_) == 0)
{
lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_668_; 
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_659_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v___x_659_, 0);
lean_dec(v_unused_669_);
v___x_662_ = v___x_659_;
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
else
{
lean_dec(v___x_659_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_668_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_666_; 
v___x_664_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_664_, 0, v_mvarId_649_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 0, v___x_664_);
v___x_666_ = v___x_662_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
else
{
lean_dec(v_a_660_);
lean_dec(v_mvarId_649_);
return v___x_659_;
}
}
else
{
lean_dec(v_mvarId_649_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalIgnoringNoProgress___boxed(lean_object* v_mvarId_670_, lean_object* v_methods_671_, lean_object* v_config_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_Sym_simpGoalIgnoringNoProgress(v_mvarId_670_, v_methods_671_, v_config_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
return v_res_680_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Goal(builtin);
}
#ifdef __cplusplus
}
#endif
