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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2;
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
lean_dec_ref(v_t_7_);
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
v___x_52_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_51_);
lean_ctor_set(v___x_52_, 2, v___x_51_);
lean_ctor_set(v___x_52_, 3, v___x_50_);
lean_ctor_set(v___x_52_, 4, v___x_50_);
lean_ctor_set(v___x_52_, 5, v___x_50_);
lean_ctor_set(v___x_52_, 6, v___x_50_);
lean_ctor_set(v___x_52_, 7, v___x_50_);
lean_ctor_set(v___x_52_, 8, v___x_50_);
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
lean_object* v___x_70_; lean_object* v_env_71_; lean_object* v_options_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_70_ = lean_st_ref_get(v___y_68_);
v_env_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_env_71_);
lean_dec(v___x_70_);
v_options_72_ = lean_ctor_get(v___y_67_, 2);
v___x_73_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2);
v___x_74_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_72_);
v___x_75_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_75_, 0, v_env_71_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
lean_ctor_set(v___x_75_, 2, v___x_74_);
lean_ctor_set(v___x_75_, 3, v_options_72_);
v___x_76_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v_msgData_66_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___boxed(lean_object* v_msgData_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(v_msgData_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(lean_object* v_msg_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_ref_87_; lean_object* v___x_88_; lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_97_; 
v_ref_87_ = lean_ctor_get(v___y_84_, 5);
v___x_88_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(v_msg_83_, v___y_84_, v___y_85_);
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_97_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
lean_inc(v_ref_87_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v_ref_87_);
lean_ctor_set(v___x_93_, 1, v_a_89_);
if (v_isShared_92_ == 0)
{
lean_ctor_set_tag(v___x_91_, 1);
lean_ctor_set(v___x_91_, 0, v___x_93_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg___boxed(lean_object* v_msg_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(v_msg_98_, v___y_99_, v___y_100_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_99_);
return v_res_102_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = ((lean_object*)(l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__0));
v___x_105_ = l_Lean_stringToMessageData(v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_toOption(lean_object* v_x_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
switch(lean_obj_tag(v_x_106_))
{
case 0:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_obj_once(&l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1, &l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1_once, _init_l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1);
v___x_111_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(v___x_110_, v_a_107_, v_a_108_);
return v___x_111_;
}
case 1:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_box(0);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
default: 
{
lean_object* v_mvarId_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_122_; 
v_mvarId_114_ = lean_ctor_get(v_x_106_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_106_);
if (v_isSharedCheck_122_ == 0)
{
v___x_116_ = v_x_106_;
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_mvarId_114_);
lean_dec(v_x_106_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_122_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 1);
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_mvarId_114_);
v___x_119_ = v_reuseFailAlloc_121_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; 
v___x_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
return v___x_120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_toOption___boxed(lean_object* v_x_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Meta_Sym_SimpGoalResult_toOption(v_x_123_, v_a_124_, v_a_125_);
lean_dec(v_a_125_);
lean_dec_ref(v_a_124_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0(lean_object* v_00_u03b1_128_, lean_object* v_msg_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(v_msg_129_, v___y_130_, v___y_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___boxed(lean_object* v_00_u03b1_134_, lean_object* v_msg_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0(v_00_u03b1_134_, v_msg_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress(lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
if (lean_obj_tag(v_x_140_) == 0)
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_142_, 0, v_x_141_);
return v___x_142_;
}
else
{
lean_dec(v_x_141_);
lean_inc(v_x_140_);
return v_x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress___boxed(lean_object* v_x_143_, lean_object* v_x_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress(v_x_143_, v_x_144_);
lean_dec(v_x_143_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
lean_object* v_ks_150_; lean_object* v_vs_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_175_; 
v_ks_150_ = lean_ctor_get(v_x_146_, 0);
v_vs_151_ = lean_ctor_get(v_x_146_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v_x_146_);
if (v_isSharedCheck_175_ == 0)
{
v___x_153_ = v_x_146_;
v_isShared_154_ = v_isSharedCheck_175_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_vs_151_);
lean_inc(v_ks_150_);
lean_dec(v_x_146_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_175_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = lean_array_get_size(v_ks_150_);
v___x_156_ = lean_nat_dec_lt(v_x_147_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
lean_dec(v_x_147_);
v___x_157_ = lean_array_push(v_ks_150_, v_x_148_);
v___x_158_ = lean_array_push(v_vs_151_, v_x_149_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v___x_158_);
lean_ctor_set(v___x_153_, 0, v___x_157_);
v___x_160_ = v___x_153_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v___x_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
else
{
lean_object* v_k_x27_162_; uint8_t v___x_163_; 
v_k_x27_162_ = lean_array_fget_borrowed(v_ks_150_, v_x_147_);
v___x_163_ = l_Lean_instBEqMVarId_beq(v_x_148_, v_k_x27_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_165_; 
if (v_isShared_154_ == 0)
{
v___x_165_ = v___x_153_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_ks_150_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_vs_151_);
v___x_165_ = v_reuseFailAlloc_169_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v_x_147_, v___x_166_);
lean_dec(v_x_147_);
v_x_146_ = v___x_165_;
v_x_147_ = v___x_167_;
goto _start;
}
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_170_ = lean_array_fset(v_ks_150_, v_x_147_, v_x_148_);
v___x_171_ = lean_array_fset(v_vs_151_, v_x_147_, v_x_149_);
lean_dec(v_x_147_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v___x_171_);
lean_ctor_set(v___x_153_, 0, v___x_170_);
v___x_173_ = v___x_153_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_176_, lean_object* v_k_177_, lean_object* v_v_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_unsigned_to_nat(0u);
v___x_180_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_176_, v___x_179_, v_k_177_, v_v_178_);
return v___x_180_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_181_; size_t v___x_182_; size_t v___x_183_; 
v___x_181_ = ((size_t)5ULL);
v___x_182_ = ((size_t)1ULL);
v___x_183_ = lean_usize_shift_left(v___x_182_, v___x_181_);
return v___x_183_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_184_; size_t v___x_185_; size_t v___x_186_; 
v___x_184_ = ((size_t)1ULL);
v___x_185_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_186_ = lean_usize_sub(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(lean_object* v_x_188_, size_t v_x_189_, size_t v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
if (lean_obj_tag(v_x_188_) == 0)
{
lean_object* v_es_193_; size_t v___x_194_; size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; lean_object* v_j_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_es_193_ = lean_ctor_get(v_x_188_, 0);
v___x_194_ = ((size_t)5ULL);
v___x_195_ = ((size_t)1ULL);
v___x_196_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_197_ = lean_usize_land(v_x_189_, v___x_196_);
v_j_198_ = lean_usize_to_nat(v___x_197_);
v___x_199_ = lean_array_get_size(v_es_193_);
v___x_200_ = lean_nat_dec_lt(v_j_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_dec(v_j_198_);
lean_dec(v_x_192_);
lean_dec(v_x_191_);
return v_x_188_;
}
else
{
lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_237_; 
lean_inc_ref(v_es_193_);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v_x_188_, 0);
lean_dec(v_unused_238_);
v___x_202_ = v_x_188_;
v_isShared_203_ = v_isSharedCheck_237_;
goto v_resetjp_201_;
}
else
{
lean_dec(v_x_188_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_237_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v_v_204_; lean_object* v___x_205_; lean_object* v_xs_x27_206_; lean_object* v___y_208_; 
v_v_204_ = lean_array_fget(v_es_193_, v_j_198_);
v___x_205_ = lean_box(0);
v_xs_x27_206_ = lean_array_fset(v_es_193_, v_j_198_, v___x_205_);
switch(lean_obj_tag(v_v_204_))
{
case 0:
{
lean_object* v_key_213_; lean_object* v_val_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_224_; 
v_key_213_ = lean_ctor_get(v_v_204_, 0);
v_val_214_ = lean_ctor_get(v_v_204_, 1);
v_isSharedCheck_224_ = !lean_is_exclusive(v_v_204_);
if (v_isSharedCheck_224_ == 0)
{
v___x_216_ = v_v_204_;
v_isShared_217_ = v_isSharedCheck_224_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_val_214_);
lean_inc(v_key_213_);
lean_dec(v_v_204_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_224_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
uint8_t v___x_218_; 
v___x_218_ = l_Lean_instBEqMVarId_beq(v_x_191_, v_key_213_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_del_object(v___x_216_);
v___x_219_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_213_, v_val_214_, v_x_191_, v_x_192_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
v___y_208_ = v___x_220_;
goto v___jp_207_;
}
else
{
lean_object* v___x_222_; 
lean_dec(v_val_214_);
lean_dec(v_key_213_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v_x_192_);
lean_ctor_set(v___x_216_, 0, v_x_191_);
v___x_222_ = v___x_216_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_x_191_);
lean_ctor_set(v_reuseFailAlloc_223_, 1, v_x_192_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
v___y_208_ = v___x_222_;
goto v___jp_207_;
}
}
}
}
case 1:
{
lean_object* v_node_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_235_; 
v_node_225_ = lean_ctor_get(v_v_204_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_v_204_);
if (v_isSharedCheck_235_ == 0)
{
v___x_227_ = v_v_204_;
v_isShared_228_ = v_isSharedCheck_235_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_node_225_);
lean_dec(v_v_204_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_235_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
size_t v___x_229_; size_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_229_ = lean_usize_shift_right(v_x_189_, v___x_194_);
v___x_230_ = lean_usize_add(v_x_190_, v___x_195_);
v___x_231_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_node_225_, v___x_229_, v___x_230_, v_x_191_, v_x_192_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_231_);
v___x_233_ = v___x_227_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
v___y_208_ = v___x_233_;
goto v___jp_207_;
}
}
}
default: 
{
lean_object* v___x_236_; 
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_x_191_);
lean_ctor_set(v___x_236_, 1, v_x_192_);
v___y_208_ = v___x_236_;
goto v___jp_207_;
}
}
v___jp_207_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_array_fset(v_xs_x27_206_, v_j_198_, v___y_208_);
lean_dec(v_j_198_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 0, v___x_209_);
v___x_211_ = v___x_202_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
else
{
lean_object* v_ks_239_; lean_object* v_vs_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_260_; 
v_ks_239_ = lean_ctor_get(v_x_188_, 0);
v_vs_240_ = lean_ctor_get(v_x_188_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_188_);
if (v_isSharedCheck_260_ == 0)
{
v___x_242_ = v_x_188_;
v_isShared_243_ = v_isSharedCheck_260_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_vs_240_);
lean_inc(v_ks_239_);
lean_dec(v_x_188_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_260_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_ks_239_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_vs_240_);
v___x_245_ = v_reuseFailAlloc_259_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v_newNode_246_; uint8_t v___y_248_; size_t v___x_254_; uint8_t v___x_255_; 
v_newNode_246_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(v___x_245_, v_x_191_, v_x_192_);
v___x_254_ = ((size_t)7ULL);
v___x_255_ = lean_usize_dec_le(v___x_254_, v_x_190_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_256_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_246_);
v___x_257_ = lean_unsigned_to_nat(4u);
v___x_258_ = lean_nat_dec_lt(v___x_256_, v___x_257_);
lean_dec(v___x_256_);
v___y_248_ = v___x_258_;
goto v___jp_247_;
}
else
{
v___y_248_ = v___x_255_;
goto v___jp_247_;
}
v___jp_247_:
{
if (v___y_248_ == 0)
{
lean_object* v_ks_249_; lean_object* v_vs_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_ks_249_ = lean_ctor_get(v_newNode_246_, 0);
lean_inc_ref(v_ks_249_);
v_vs_250_ = lean_ctor_get(v_newNode_246_, 1);
lean_inc_ref(v_vs_250_);
lean_dec_ref(v_newNode_246_);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_253_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_x_190_, v_ks_249_, v_vs_250_, v___x_251_, v___x_252_);
lean_dec_ref(v_vs_250_);
lean_dec_ref(v_ks_249_);
return v___x_253_;
}
else
{
return v_newNode_246_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_261_, lean_object* v_keys_262_, lean_object* v_vals_263_, lean_object* v_i_264_, lean_object* v_entries_265_){
_start:
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_get_size(v_keys_262_);
v___x_267_ = lean_nat_dec_lt(v_i_264_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v_i_264_);
return v_entries_265_;
}
else
{
lean_object* v_k_268_; lean_object* v_v_269_; uint64_t v___x_270_; size_t v_h_271_; size_t v___x_272_; lean_object* v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v_h_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v_k_268_ = lean_array_fget_borrowed(v_keys_262_, v_i_264_);
v_v_269_ = lean_array_fget_borrowed(v_vals_263_, v_i_264_);
v___x_270_ = l_Lean_instHashableMVarId_hash(v_k_268_);
v_h_271_ = lean_uint64_to_usize(v___x_270_);
v___x_272_ = ((size_t)5ULL);
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_sub(v_depth_261_, v___x_274_);
v___x_276_ = lean_usize_mul(v___x_272_, v___x_275_);
v_h_277_ = lean_usize_shift_right(v_h_271_, v___x_276_);
v___x_278_ = lean_nat_add(v_i_264_, v___x_273_);
lean_dec(v_i_264_);
lean_inc(v_v_269_);
lean_inc(v_k_268_);
v___x_279_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_entries_265_, v_h_277_, v_depth_261_, v_k_268_, v_v_269_);
v_i_264_ = v___x_278_;
v_entries_265_ = v___x_279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_281_, lean_object* v_keys_282_, lean_object* v_vals_283_, lean_object* v_i_284_, lean_object* v_entries_285_){
_start:
{
size_t v_depth_boxed_286_; lean_object* v_res_287_; 
v_depth_boxed_286_ = lean_unbox_usize(v_depth_281_);
lean_dec(v_depth_281_);
v_res_287_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_286_, v_keys_282_, v_vals_283_, v_i_284_, v_entries_285_);
lean_dec_ref(v_vals_283_);
lean_dec_ref(v_keys_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
size_t v_x_3408__boxed_293_; size_t v_x_3409__boxed_294_; lean_object* v_res_295_; 
v_x_3408__boxed_293_ = lean_unbox_usize(v_x_289_);
lean_dec(v_x_289_);
v_x_3409__boxed_294_ = lean_unbox_usize(v_x_290_);
lean_dec(v_x_290_);
v_res_295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_288_, v_x_3408__boxed_293_, v_x_3409__boxed_294_, v_x_291_, v_x_292_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
uint64_t v___x_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v___x_302_; 
v___x_299_ = l_Lean_instHashableMVarId_hash(v_x_297_);
v___x_300_ = lean_uint64_to_usize(v___x_299_);
v___x_301_ = ((size_t)1ULL);
v___x_302_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_296_, v___x_300_, v___x_301_, v_x_297_, v_x_298_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(lean_object* v_mvarId_303_, lean_object* v_val_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v_mctx_308_; lean_object* v_cache_309_; lean_object* v_zetaDeltaFVarIds_310_; lean_object* v_postponed_311_; lean_object* v_diag_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_339_; 
v___x_307_ = lean_st_ref_take(v___y_305_);
v_mctx_308_ = lean_ctor_get(v___x_307_, 0);
v_cache_309_ = lean_ctor_get(v___x_307_, 1);
v_zetaDeltaFVarIds_310_ = lean_ctor_get(v___x_307_, 2);
v_postponed_311_ = lean_ctor_get(v___x_307_, 3);
v_diag_312_ = lean_ctor_get(v___x_307_, 4);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_339_ == 0)
{
v___x_314_ = v___x_307_;
v_isShared_315_ = v_isSharedCheck_339_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_diag_312_);
lean_inc(v_postponed_311_);
lean_inc(v_zetaDeltaFVarIds_310_);
lean_inc(v_cache_309_);
lean_inc(v_mctx_308_);
lean_dec(v___x_307_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_339_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v_depth_316_; lean_object* v_levelAssignDepth_317_; lean_object* v_mvarCounter_318_; lean_object* v_lDepth_319_; lean_object* v_decls_320_; lean_object* v_userNames_321_; lean_object* v_lAssignment_322_; lean_object* v_eAssignment_323_; lean_object* v_dAssignment_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_338_; 
v_depth_316_ = lean_ctor_get(v_mctx_308_, 0);
v_levelAssignDepth_317_ = lean_ctor_get(v_mctx_308_, 1);
v_mvarCounter_318_ = lean_ctor_get(v_mctx_308_, 2);
v_lDepth_319_ = lean_ctor_get(v_mctx_308_, 3);
v_decls_320_ = lean_ctor_get(v_mctx_308_, 4);
v_userNames_321_ = lean_ctor_get(v_mctx_308_, 5);
v_lAssignment_322_ = lean_ctor_get(v_mctx_308_, 6);
v_eAssignment_323_ = lean_ctor_get(v_mctx_308_, 7);
v_dAssignment_324_ = lean_ctor_get(v_mctx_308_, 8);
v_isSharedCheck_338_ = !lean_is_exclusive(v_mctx_308_);
if (v_isSharedCheck_338_ == 0)
{
v___x_326_ = v_mctx_308_;
v_isShared_327_ = v_isSharedCheck_338_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_dAssignment_324_);
lean_inc(v_eAssignment_323_);
lean_inc(v_lAssignment_322_);
lean_inc(v_userNames_321_);
lean_inc(v_decls_320_);
lean_inc(v_lDepth_319_);
lean_inc(v_mvarCounter_318_);
lean_inc(v_levelAssignDepth_317_);
lean_inc(v_depth_316_);
lean_dec(v_mctx_308_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_338_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(v_eAssignment_323_, v_mvarId_303_, v_val_304_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 7, v___x_328_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_depth_316_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_levelAssignDepth_317_);
lean_ctor_set(v_reuseFailAlloc_337_, 2, v_mvarCounter_318_);
lean_ctor_set(v_reuseFailAlloc_337_, 3, v_lDepth_319_);
lean_ctor_set(v_reuseFailAlloc_337_, 4, v_decls_320_);
lean_ctor_set(v_reuseFailAlloc_337_, 5, v_userNames_321_);
lean_ctor_set(v_reuseFailAlloc_337_, 6, v_lAssignment_322_);
lean_ctor_set(v_reuseFailAlloc_337_, 7, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_337_, 8, v_dAssignment_324_);
v___x_330_ = v_reuseFailAlloc_337_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_332_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_330_);
v___x_332_ = v___x_314_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_cache_309_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v_zetaDeltaFVarIds_310_);
lean_ctor_set(v_reuseFailAlloc_336_, 3, v_postponed_311_);
lean_ctor_set(v_reuseFailAlloc_336_, 4, v_diag_312_);
v___x_332_ = v_reuseFailAlloc_336_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = lean_st_ref_set(v___y_305_, v___x_332_);
v___x_334_ = lean_box(0);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg___boxed(lean_object* v_mvarId_340_, lean_object* v_val_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_340_, v_val_341_, v___y_342_);
lean_dec(v___y_342_);
return v_res_344_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_355_ = lean_box(0);
v___x_356_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5));
v___x_357_ = l_Lean_mkConst(v___x_356_, v___x_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object* v_result_358_, lean_object* v_mvarId_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_367_; 
lean_inc(v_mvarId_359_);
v___x_367_ = l_Lean_MVarId_getDecl(v_mvarId_359_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
if (lean_obj_tag(v___x_367_) == 0)
{
if (lean_obj_tag(v_result_358_) == 0)
{
lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref(v_result_358_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_mvarId_359_);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v___x_367_, 0);
lean_dec(v_unused_376_);
v___x_369_ = v___x_367_;
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
else
{
lean_dec(v___x_367_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_375_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_box(0);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_object* v_a_377_; lean_object* v_e_x27_378_; lean_object* v_proof_379_; lean_object* v_userName_380_; lean_object* v_type_381_; lean_object* v___x_382_; 
v_a_377_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_377_);
lean_dec_ref(v___x_367_);
v_e_x27_378_ = lean_ctor_get(v_result_358_, 0);
lean_inc_ref(v_e_x27_378_);
v_proof_379_ = lean_ctor_get(v_result_358_, 1);
lean_inc_ref(v_proof_379_);
lean_dec_ref(v_result_358_);
v_userName_380_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_userName_380_);
v_type_381_ = lean_ctor_get(v_a_377_, 2);
lean_inc_ref(v_type_381_);
lean_dec(v_a_377_);
lean_inc_ref(v_a_362_);
lean_inc_ref(v_e_x27_378_);
v___x_382_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_e_x27_378_, v_userName_380_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref(v___x_382_);
lean_inc(v_a_363_);
lean_inc_ref(v_type_381_);
v___x_384_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_381_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_413_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref(v___x_384_);
v___x_386_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2));
v___x_387_ = lean_box(0);
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v_a_385_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_mkConst(v___x_386_, v___x_388_);
lean_inc(v_a_383_);
lean_inc_ref(v_e_x27_378_);
v___x_390_ = l_Lean_mkApp4(v___x_389_, v_type_381_, v_e_x27_378_, v_proof_379_, v_a_383_);
v___x_391_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_359_, v___x_390_, v_a_363_);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v___x_391_, 0);
lean_dec(v_unused_414_);
v___x_393_ = v___x_391_;
v_isShared_394_ = v_isSharedCheck_413_;
goto v_resetjp_392_;
}
else
{
lean_dec(v___x_391_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_413_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
uint8_t v___x_395_; 
v___x_395_ = l_Lean_Expr_isTrue(v_e_x27_378_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
lean_dec(v_a_363_);
v___x_396_ = l_Lean_Expr_mvarId_x21(v_a_383_);
lean_dec(v_a_383_);
v___x_397_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_397_);
v___x_399_ = v___x_393_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
lean_del_object(v___x_393_);
v___x_401_ = l_Lean_Expr_mvarId_x21(v_a_383_);
lean_dec(v_a_383_);
v___x_402_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6, &l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6_once, _init_l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6);
v___x_403_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v___x_401_, v___x_402_, v_a_363_);
lean_dec(v_a_363_);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_403_, 0);
lean_dec(v_unused_412_);
v___x_405_ = v___x_403_;
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
else
{
lean_dec(v___x_403_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = lean_box(1);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec(v_a_383_);
lean_dec_ref(v_type_381_);
lean_dec_ref(v_proof_379_);
lean_dec_ref(v_e_x27_378_);
lean_dec(v_a_363_);
lean_dec(v_mvarId_359_);
v_a_415_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_384_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_384_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_type_381_);
lean_dec_ref(v_proof_379_);
lean_dec_ref(v_e_x27_378_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_mvarId_359_);
v_a_423_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_382_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_382_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
else
{
lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_438_; 
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec(v_a_363_);
lean_dec_ref(v_a_362_);
lean_dec(v_mvarId_359_);
lean_dec_ref(v_result_358_);
v_a_431_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_438_ == 0)
{
v___x_433_ = v___x_367_;
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_367_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_438_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___boxed(lean_object* v_result_439_, lean_object* v_mvarId_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_result_439_, v_mvarId_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0(lean_object* v_mvarId_449_, lean_object* v_val_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_449_, v_val_450_, v___y_454_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___boxed(lean_object* v_mvarId_459_, lean_object* v_val_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0(v_mvarId_459_, v_val_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0(lean_object* v_00_u03b2_469_, lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(v_x_470_, v_x_471_, v_x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_474_, lean_object* v_x_475_, size_t v_x_476_, size_t v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_475_, v_x_476_, v_x_477_, v_x_478_, v_x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
size_t v_x_3864__boxed_487_; size_t v_x_3865__boxed_488_; lean_object* v_res_489_; 
v_x_3864__boxed_487_ = lean_unbox_usize(v_x_483_);
lean_dec(v_x_483_);
v_x_3865__boxed_488_ = lean_unbox_usize(v_x_484_);
lean_dec(v_x_484_);
v_res_489_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1(v_00_u03b2_481_, v_x_482_, v_x_3864__boxed_487_, v_x_3865__boxed_488_, v_x_485_, v_x_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_490_, lean_object* v_n_491_, lean_object* v_k_492_, lean_object* v_v_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(v_n_491_, v_k_492_, v_v_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_495_, size_t v_depth_496_, lean_object* v_keys_497_, lean_object* v_vals_498_, lean_object* v_heq_499_, lean_object* v_i_500_, lean_object* v_entries_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_496_, v_keys_497_, v_vals_498_, v_i_500_, v_entries_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_503_, lean_object* v_depth_504_, lean_object* v_keys_505_, lean_object* v_vals_506_, lean_object* v_heq_507_, lean_object* v_i_508_, lean_object* v_entries_509_){
_start:
{
size_t v_depth_boxed_510_; lean_object* v_res_511_; 
v_depth_boxed_510_ = lean_unbox_usize(v_depth_504_);
lean_dec(v_depth_504_);
v_res_511_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_503_, v_depth_boxed_510_, v_keys_505_, v_vals_506_, v_heq_507_, v_i_508_, v_entries_509_);
lean_dec_ref(v_vals_506_);
lean_dec_ref(v_keys_505_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_512_, lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_513_, v_x_514_, v_x_515_, v_x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0(lean_object* v_x_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = lean_apply_7(v_x_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, lean_box(0));
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0___boxed(lean_object* v_x_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0(v_x_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(lean_object* v_mvarId_536_, lean_object* v_x_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___f_545_; lean_object* v___x_546_; 
v___f_545_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_545_, 0, v_x_537_);
lean_closure_set(v___f_545_, 1, v___y_538_);
lean_closure_set(v___f_545_, 2, v___y_539_);
v___x_546_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_536_, v___f_545_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
if (lean_obj_tag(v___x_546_) == 0)
{
return v___x_546_;
}
else
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___boxed(lean_object* v_mvarId_555_, lean_object* v_x_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_555_, v_x_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0(lean_object* v_00_u03b1_565_, lean_object* v_mvarId_566_, lean_object* v_x_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_566_, v_x_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___boxed(lean_object* v_00_u03b1_576_, lean_object* v_mvarId_577_, lean_object* v_x_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0(v_00_u03b1_576_, v_mvarId_577_, v_x_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___lam__0(lean_object* v_mvarId_587_, lean_object* v_methods_588_, lean_object* v_config_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v___x_597_; 
lean_inc(v_mvarId_587_);
v___x_597_ = l_Lean_MVarId_getDecl(v_mvarId_587_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v_type_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref(v___x_597_);
v_type_599_ = lean_ctor_get(v_a_598_, 2);
lean_inc_ref(v_type_599_);
lean_dec(v_a_598_);
v___x_600_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_600_, 0, v_type_599_);
lean_inc(v___y_595_);
lean_inc_ref(v___y_594_);
lean_inc(v___y_593_);
lean_inc_ref(v___y_592_);
lean_inc(v___y_591_);
lean_inc_ref(v___y_590_);
v___x_601_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_600_, v_methods_588_, v_config_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_603_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref(v___x_601_);
v___x_603_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_a_602_, v_mvarId_587_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
return v___x_603_;
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v_mvarId_587_);
v_a_604_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_601_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_601_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec_ref(v_config_589_);
lean_dec_ref(v_methods_588_);
lean_dec(v_mvarId_587_);
v_a_612_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_597_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_597_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___lam__0___boxed(lean_object* v_mvarId_620_, lean_object* v_methods_621_, lean_object* v_config_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_Meta_Sym_simpGoal___lam__0(v_mvarId_620_, v_methods_621_, v_config_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
return v_res_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal(lean_object* v_mvarId_631_, lean_object* v_methods_632_, lean_object* v_config_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___f_641_; lean_object* v___x_642_; 
lean_inc(v_mvarId_631_);
v___f_641_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_simpGoal___lam__0___boxed), 10, 3);
lean_closure_set(v___f_641_, 0, v_mvarId_631_);
lean_closure_set(v___f_641_, 1, v_methods_632_);
lean_closure_set(v___f_641_, 2, v_config_633_);
v___x_642_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_631_, v___f_641_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___boxed(lean_object* v_mvarId_643_, lean_object* v_methods_644_, lean_object* v_config_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_643_, v_methods_644_, v_config_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalIgnoringNoProgress(lean_object* v_mvarId_654_, lean_object* v_methods_655_, lean_object* v_config_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v___x_664_; 
lean_inc(v_mvarId_654_);
v___x_664_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_654_, v_methods_655_, v_config_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
if (lean_obj_tag(v___x_664_) == 0)
{
lean_object* v_a_665_; 
v_a_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc(v_a_665_);
if (lean_obj_tag(v_a_665_) == 0)
{
lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_673_; 
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_664_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; 
v_unused_674_ = lean_ctor_get(v___x_664_, 0);
lean_dec(v_unused_674_);
v___x_667_ = v___x_664_;
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
else
{
lean_dec(v___x_664_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_673_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_669_, 0, v_mvarId_654_);
if (v_isShared_668_ == 0)
{
lean_ctor_set(v___x_667_, 0, v___x_669_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
lean_dec(v_a_665_);
lean_dec(v_mvarId_654_);
return v___x_664_;
}
}
else
{
lean_dec(v_mvarId_654_);
return v___x_664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalIgnoringNoProgress___boxed(lean_object* v_mvarId_675_, lean_object* v_methods_676_, lean_object* v_config_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Meta_Sym_simpGoalIgnoringNoProgress(v_mvarId_675_, v_methods_676_, v_config_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
return v_res_685_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Goal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
