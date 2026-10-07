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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Sym_SimpGoalResult_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 2)
{
lean_object* v_mvarId_7_; lean_object* v___x_8_; 
v_mvarId_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_mvarId_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_mvarId_7_);
return v___x_8_;
}
else
{
lean_dec(v_t_5_);
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_noProgress_elim___redArg(lean_object* v_t_21_, lean_object* v_noProgress_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_21_, v_noProgress_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_noProgress_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_noProgress_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_25_, v_noProgress_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_closed_elim___redArg(lean_object* v_t_29_, lean_object* v_closed_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_29_, v_closed_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_closed_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_closed_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_33_, v_closed_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_goal_elim___redArg(lean_object* v_t_37_, lean_object* v_goal_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_37_, v_goal_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_goal_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_goal_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Meta_Sym_SimpGoalResult_ctorElim___redArg(v_t_41_, v_goal_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_45_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__0);
v___x_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_48_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_49_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_50_);
lean_ctor_set(v___x_51_, 2, v___x_50_);
lean_ctor_set(v___x_51_, 3, v___x_50_);
lean_ctor_set(v___x_51_, 4, v___x_49_);
lean_ctor_set(v___x_51_, 5, v___x_49_);
lean_ctor_set(v___x_51_, 6, v___x_49_);
lean_ctor_set(v___x_51_, 7, v___x_49_);
lean_ctor_set(v___x_51_, 8, v___x_49_);
lean_ctor_set(v___x_51_, 9, v___x_49_);
lean_ctor_set(v___x_51_, 10, v___x_49_);
lean_ctor_set(v___x_51_, 11, v___x_48_);
return v___x_51_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_unsigned_to_nat(32u);
v___x_53_ = lean_mk_empty_array_with_capacity(v___x_52_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_55_ = ((size_t)5ULL);
v___x_56_ = lean_unsigned_to_nat(0u);
v___x_57_ = lean_unsigned_to_nat(32u);
v___x_58_ = lean_mk_empty_array_with_capacity(v___x_57_);
v___x_59_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__3);
v___x_60_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_60_, 0, v___x_59_);
lean_ctor_set(v___x_60_, 1, v___x_58_);
lean_ctor_set(v___x_60_, 2, v___x_56_);
lean_ctor_set(v___x_60_, 3, v___x_56_);
lean_ctor_set_usize(v___x_60_, 4, v___x_55_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_box(1);
v___x_62_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__4);
v___x_63_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__1);
v___x_64_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(lean_object* v_msgData_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v___x_69_; lean_object* v_toCold_70_; lean_object* v_env_71_; lean_object* v_options_72_; uint8_t v___x_73_; lean_object* v_env_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_69_ = lean_st_ref_get(v___y_67_);
v_toCold_70_ = lean_ctor_get(v___y_66_, 0);
v_env_71_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_env_71_);
lean_dec(v___x_69_);
v_options_72_ = lean_ctor_get(v_toCold_70_, 2);
v___x_73_ = 0;
v_env_74_ = l_Lean_Environment_setRecordingDeps(v_env_71_, v___x_73_);
v___x_75_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__2);
v___x_76_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_72_);
v___x_77_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_77_, 0, v_env_74_);
lean_ctor_set(v___x_77_, 1, v___x_75_);
lean_ctor_set(v___x_77_, 2, v___x_76_);
lean_ctor_set(v___x_77_, 3, v_options_72_);
v___x_78_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v_msgData_65_);
v___x_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0___boxed(lean_object* v_msgData_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(v_msgData_80_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(lean_object* v_msg_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_ref_89_; lean_object* v___x_90_; lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_99_; 
v_ref_89_ = lean_ctor_get(v___y_86_, 2);
v___x_90_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0_spec__0(v_msg_85_, v___y_86_, v___y_87_);
v_a_91_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_99_ == 0)
{
v___x_93_ = v___x_90_;
v_isShared_94_ = v_isSharedCheck_99_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_99_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_97_; 
lean_inc(v_ref_89_);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v_ref_89_);
lean_ctor_set(v___x_95_, 1, v_a_91_);
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 1);
lean_ctor_set(v___x_93_, 0, v___x_95_);
v___x_97_ = v___x_93_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg___boxed(lean_object* v_msg_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(v_msg_100_, v___y_101_, v___y_102_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_104_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = ((lean_object*)(l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__0));
v___x_107_ = l_Lean_stringToMessageData(v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_toOption(lean_object* v_x_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
switch(lean_obj_tag(v_x_108_))
{
case 0:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_obj_once(&l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1, &l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1_once, _init_l_Lean_Meta_Sym_SimpGoalResult_toOption___closed__1);
v___x_113_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(v___x_112_, v_a_109_, v_a_110_);
return v___x_113_;
}
case 1:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_box(0);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
default: 
{
lean_object* v_mvarId_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_124_; 
v_mvarId_116_ = lean_ctor_get(v_x_108_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v_x_108_);
if (v_isSharedCheck_124_ == 0)
{
v___x_118_ = v_x_108_;
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_mvarId_116_);
lean_dec(v_x_108_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_124_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 1);
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_mvarId_116_);
v___x_121_ = v_reuseFailAlloc_123_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; 
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_toOption___boxed(lean_object* v_x_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_Meta_Sym_SimpGoalResult_toOption(v_x_125_, v_a_126_, v_a_127_);
lean_dec(v_a_127_);
lean_dec_ref(v_a_126_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0(lean_object* v_00_u03b1_130_, lean_object* v_msg_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___redArg(v_msg_131_, v___y_132_, v___y_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0___boxed(lean_object* v_00_u03b1_136_, lean_object* v_msg_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_throwError___at___00Lean_Meta_Sym_SimpGoalResult_toOption_spec__0(v_00_u03b1_136_, v_msg_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_142_) == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_144_, 0, v_x_143_);
return v___x_144_;
}
else
{
lean_dec(v_x_143_);
lean_inc(v_x_142_);
return v_x_142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress___boxed(lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_Sym_SimpGoalResult_ignoreNoProgress(v_x_145_, v_x_146_);
lean_dec(v_x_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
lean_object* v_ks_152_; lean_object* v_vs_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_177_; 
v_ks_152_ = lean_ctor_get(v_x_148_, 0);
v_vs_153_ = lean_ctor_get(v_x_148_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_x_148_);
if (v_isSharedCheck_177_ == 0)
{
v___x_155_ = v_x_148_;
v_isShared_156_ = v_isSharedCheck_177_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_vs_153_);
lean_inc(v_ks_152_);
lean_dec(v_x_148_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_177_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = lean_array_get_size(v_ks_152_);
v___x_158_ = lean_nat_dec_lt(v_x_149_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
lean_dec(v_x_149_);
v___x_159_ = lean_array_push(v_ks_152_, v_x_150_);
v___x_160_ = lean_array_push(v_vs_153_, v_x_151_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___x_160_);
lean_ctor_set(v___x_155_, 0, v___x_159_);
v___x_162_ = v___x_155_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
else
{
lean_object* v_k_x27_164_; uint8_t v___x_165_; 
v_k_x27_164_ = lean_array_fget_borrowed(v_ks_152_, v_x_149_);
v___x_165_ = l_Lean_instBEqMVarId_beq(v_x_150_, v_k_x27_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_167_; 
if (v_isShared_156_ == 0)
{
v___x_167_ = v___x_155_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_ks_152_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v_vs_153_);
v___x_167_ = v_reuseFailAlloc_171_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lean_nat_add(v_x_149_, v___x_168_);
lean_dec(v_x_149_);
v_x_148_ = v___x_167_;
v_x_149_ = v___x_169_;
goto _start;
}
}
else
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v___x_172_ = lean_array_fset(v_ks_152_, v_x_149_, v_x_150_);
v___x_173_ = lean_array_fset(v_vs_153_, v_x_149_, v_x_151_);
lean_dec(v_x_149_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 1, v___x_173_);
lean_ctor_set(v___x_155_, 0, v___x_172_);
v___x_175_ = v___x_155_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_178_, lean_object* v_k_179_, lean_object* v_v_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_178_, v___x_181_, v_k_179_, v_v_180_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(lean_object* v_x_184_, size_t v_x_185_, size_t v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_){
_start:
{
if (lean_obj_tag(v_x_184_) == 0)
{
lean_object* v_es_189_; size_t v___x_190_; size_t v___x_191_; lean_object* v_j_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_es_189_ = lean_ctor_get(v_x_184_, 0);
v___x_190_ = ((size_t)31ULL);
v___x_191_ = lean_usize_land(v_x_185_, v___x_190_);
v_j_192_ = lean_usize_to_nat(v___x_191_);
v___x_193_ = lean_array_get_size(v_es_189_);
v___x_194_ = lean_nat_dec_lt(v_j_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_dec(v_j_192_);
lean_dec(v_x_188_);
lean_dec(v_x_187_);
return v_x_184_;
}
else
{
lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_233_; 
lean_inc_ref(v_es_189_);
v_isSharedCheck_233_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; 
v_unused_234_ = lean_ctor_get(v_x_184_, 0);
lean_dec(v_unused_234_);
v___x_196_ = v_x_184_;
v_isShared_197_ = v_isSharedCheck_233_;
goto v_resetjp_195_;
}
else
{
lean_dec(v_x_184_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_233_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v_v_198_; lean_object* v___x_199_; lean_object* v_xs_x27_200_; lean_object* v___y_202_; 
v_v_198_ = lean_array_fget(v_es_189_, v_j_192_);
v___x_199_ = lean_box(0);
v_xs_x27_200_ = lean_array_fset(v_es_189_, v_j_192_, v___x_199_);
switch(lean_obj_tag(v_v_198_))
{
case 0:
{
lean_object* v_key_207_; lean_object* v_val_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_218_; 
v_key_207_ = lean_ctor_get(v_v_198_, 0);
v_val_208_ = lean_ctor_get(v_v_198_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_v_198_);
if (v_isSharedCheck_218_ == 0)
{
v___x_210_ = v_v_198_;
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_val_208_);
lean_inc(v_key_207_);
lean_dec(v_v_198_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_218_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
uint8_t v___x_212_; 
v___x_212_ = l_Lean_instBEqMVarId_beq(v_x_187_, v_key_207_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_del_object(v___x_210_);
v___x_213_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_207_, v_val_208_, v_x_187_, v_x_188_);
v___x_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
v___y_202_ = v___x_214_;
goto v___jp_201_;
}
else
{
lean_object* v___x_216_; 
lean_dec(v_val_208_);
lean_dec(v_key_207_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 1, v_x_188_);
lean_ctor_set(v___x_210_, 0, v_x_187_);
v___x_216_ = v___x_210_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_x_187_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_x_188_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
v___y_202_ = v___x_216_;
goto v___jp_201_;
}
}
}
}
case 1:
{
lean_object* v_node_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_231_; 
v_node_219_ = lean_ctor_get(v_v_198_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v_v_198_);
if (v_isSharedCheck_231_ == 0)
{
v___x_221_ = v_v_198_;
v_isShared_222_ = v_isSharedCheck_231_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_node_219_);
lean_dec(v_v_198_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_231_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
size_t v___x_223_; size_t v___x_224_; size_t v___x_225_; size_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_223_ = ((size_t)5ULL);
v___x_224_ = lean_usize_shift_right(v_x_185_, v___x_223_);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_add(v_x_186_, v___x_225_);
v___x_227_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_node_219_, v___x_224_, v___x_226_, v_x_187_, v_x_188_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_227_);
v___x_229_ = v___x_221_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
v___y_202_ = v___x_229_;
goto v___jp_201_;
}
}
}
default: 
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_x_187_);
lean_ctor_set(v___x_232_, 1, v_x_188_);
v___y_202_ = v___x_232_;
goto v___jp_201_;
}
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_203_ = lean_array_fset(v_xs_x27_200_, v_j_192_, v___y_202_);
lean_dec(v_j_192_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_203_);
v___x_205_ = v___x_196_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
else
{
lean_object* v_ks_235_; lean_object* v_vs_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_254_; 
v_ks_235_ = lean_ctor_get(v_x_184_, 0);
v_vs_236_ = lean_ctor_get(v_x_184_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v_x_184_);
if (v_isSharedCheck_254_ == 0)
{
v___x_238_ = v_x_184_;
v_isShared_239_ = v_isSharedCheck_254_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_vs_236_);
lean_inc(v_ks_235_);
lean_dec(v_x_184_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_254_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_ks_235_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_vs_236_);
v___x_241_ = v_reuseFailAlloc_253_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v_newNode_242_; size_t v___x_243_; uint8_t v___x_244_; 
v_newNode_242_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(v___x_241_, v_x_187_, v_x_188_);
v___x_243_ = ((size_t)7ULL);
v___x_244_ = lean_usize_dec_le(v___x_243_, v_x_186_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v___x_245_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_242_);
v___x_246_ = lean_unsigned_to_nat(4u);
v___x_247_ = lean_nat_dec_lt(v___x_245_, v___x_246_);
lean_dec(v___x_245_);
if (v___x_247_ == 0)
{
lean_object* v_ks_248_; lean_object* v_vs_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_ks_248_ = lean_ctor_get(v_newNode_242_, 0);
lean_inc_ref(v_ks_248_);
v_vs_249_ = lean_ctor_get(v_newNode_242_, 1);
lean_inc_ref(v_vs_249_);
lean_dec_ref(v_newNode_242_);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_252_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_x_186_, v_ks_248_, v_vs_249_, v___x_250_, v___x_251_);
lean_dec_ref(v_vs_249_);
lean_dec_ref(v_ks_248_);
return v___x_252_;
}
else
{
return v_newNode_242_;
}
}
else
{
return v_newNode_242_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_255_, lean_object* v_keys_256_, lean_object* v_vals_257_, lean_object* v_i_258_, lean_object* v_entries_259_){
_start:
{
lean_object* v___x_260_; uint8_t v___x_261_; 
v___x_260_ = lean_array_get_size(v_keys_256_);
v___x_261_ = lean_nat_dec_lt(v_i_258_, v___x_260_);
if (v___x_261_ == 0)
{
lean_dec(v_i_258_);
return v_entries_259_;
}
else
{
lean_object* v_k_262_; lean_object* v_v_263_; uint64_t v___x_264_; size_t v_h_265_; size_t v___x_266_; lean_object* v___x_267_; size_t v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v_h_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_k_262_ = lean_array_fget_borrowed(v_keys_256_, v_i_258_);
v_v_263_ = lean_array_fget_borrowed(v_vals_257_, v_i_258_);
v___x_264_ = l_Lean_instHashableMVarId_hash(v_k_262_);
v_h_265_ = lean_uint64_to_usize(v___x_264_);
v___x_266_ = ((size_t)5ULL);
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_sub(v_depth_255_, v___x_268_);
v___x_270_ = lean_usize_mul(v___x_266_, v___x_269_);
v_h_271_ = lean_usize_shift_right(v_h_265_, v___x_270_);
v___x_272_ = lean_nat_add(v_i_258_, v___x_267_);
lean_dec(v_i_258_);
lean_inc(v_v_263_);
lean_inc(v_k_262_);
v___x_273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_entries_259_, v_h_271_, v_depth_255_, v_k_262_, v_v_263_);
v_i_258_ = v___x_272_;
v_entries_259_ = v___x_273_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_275_, lean_object* v_keys_276_, lean_object* v_vals_277_, lean_object* v_i_278_, lean_object* v_entries_279_){
_start:
{
size_t v_depth_boxed_280_; lean_object* v_res_281_; 
v_depth_boxed_280_ = lean_unbox_usize(v_depth_275_);
lean_dec(v_depth_275_);
v_res_281_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_280_, v_keys_276_, v_vals_277_, v_i_278_, v_entries_279_);
lean_dec_ref(v_vals_277_);
lean_dec_ref(v_keys_276_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
size_t v_x_3125__boxed_287_; size_t v_x_3126__boxed_288_; lean_object* v_res_289_; 
v_x_3125__boxed_287_ = lean_unbox_usize(v_x_283_);
lean_dec(v_x_283_);
v_x_3126__boxed_288_ = lean_unbox_usize(v_x_284_);
lean_dec(v_x_284_);
v_res_289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_282_, v_x_3125__boxed_287_, v_x_3126__boxed_288_, v_x_285_, v_x_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
uint64_t v___x_293_; size_t v___x_294_; size_t v___x_295_; lean_object* v___x_296_; 
v___x_293_ = l_Lean_instHashableMVarId_hash(v_x_291_);
v___x_294_ = lean_uint64_to_usize(v___x_293_);
v___x_295_ = ((size_t)1ULL);
v___x_296_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_290_, v___x_294_, v___x_295_, v_x_291_, v_x_292_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(lean_object* v_mvarId_297_, lean_object* v_val_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; lean_object* v_mctx_302_; lean_object* v_cache_303_; lean_object* v_zetaDeltaFVarIds_304_; lean_object* v_postponed_305_; lean_object* v_diag_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_336_; 
v___x_301_ = lean_st_ref_take(v___y_299_);
v_mctx_302_ = lean_ctor_get(v___x_301_, 0);
v_cache_303_ = lean_ctor_get(v___x_301_, 1);
v_zetaDeltaFVarIds_304_ = lean_ctor_get(v___x_301_, 2);
v_postponed_305_ = lean_ctor_get(v___x_301_, 3);
v_diag_306_ = lean_ctor_get(v___x_301_, 4);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_336_ == 0)
{
v___x_308_ = v___x_301_;
v_isShared_309_ = v_isSharedCheck_336_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_diag_306_);
lean_inc(v_postponed_305_);
lean_inc(v_zetaDeltaFVarIds_304_);
lean_inc(v_cache_303_);
lean_inc(v_mctx_302_);
lean_dec(v___x_301_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_336_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_depth_310_; lean_object* v_levelAssignDepth_311_; lean_object* v_lmvarCounter_312_; lean_object* v_mvarCounter_313_; lean_object* v_lDecls_314_; lean_object* v_decls_315_; lean_object* v_userNames_316_; lean_object* v_lAssignment_317_; lean_object* v_eAssignment_318_; lean_object* v_dAssignment_319_; lean_object* v_instanceTypedMVars_320_; lean_object* v_synthNormMemo_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_335_; 
v_depth_310_ = lean_ctor_get(v_mctx_302_, 0);
v_levelAssignDepth_311_ = lean_ctor_get(v_mctx_302_, 1);
v_lmvarCounter_312_ = lean_ctor_get(v_mctx_302_, 2);
v_mvarCounter_313_ = lean_ctor_get(v_mctx_302_, 3);
v_lDecls_314_ = lean_ctor_get(v_mctx_302_, 4);
v_decls_315_ = lean_ctor_get(v_mctx_302_, 5);
v_userNames_316_ = lean_ctor_get(v_mctx_302_, 6);
v_lAssignment_317_ = lean_ctor_get(v_mctx_302_, 7);
v_eAssignment_318_ = lean_ctor_get(v_mctx_302_, 8);
v_dAssignment_319_ = lean_ctor_get(v_mctx_302_, 9);
v_instanceTypedMVars_320_ = lean_ctor_get(v_mctx_302_, 10);
v_synthNormMemo_321_ = lean_ctor_get(v_mctx_302_, 11);
v_isSharedCheck_335_ = !lean_is_exclusive(v_mctx_302_);
if (v_isSharedCheck_335_ == 0)
{
v___x_323_ = v_mctx_302_;
v_isShared_324_ = v_isSharedCheck_335_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_synthNormMemo_321_);
lean_inc(v_instanceTypedMVars_320_);
lean_inc(v_dAssignment_319_);
lean_inc(v_eAssignment_318_);
lean_inc(v_lAssignment_317_);
lean_inc(v_userNames_316_);
lean_inc(v_decls_315_);
lean_inc(v_lDecls_314_);
lean_inc(v_mvarCounter_313_);
lean_inc(v_lmvarCounter_312_);
lean_inc(v_levelAssignDepth_311_);
lean_inc(v_depth_310_);
lean_dec(v_mctx_302_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_335_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = lean_box(0);
v___x_326_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(v_eAssignment_318_, v_mvarId_297_, v_val_298_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 8, v___x_326_);
v___x_328_ = v___x_323_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_depth_310_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_levelAssignDepth_311_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_lmvarCounter_312_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_mvarCounter_313_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_lDecls_314_);
lean_ctor_set(v_reuseFailAlloc_334_, 5, v_decls_315_);
lean_ctor_set(v_reuseFailAlloc_334_, 6, v_userNames_316_);
lean_ctor_set(v_reuseFailAlloc_334_, 7, v_lAssignment_317_);
lean_ctor_set(v_reuseFailAlloc_334_, 8, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_334_, 9, v_dAssignment_319_);
lean_ctor_set(v_reuseFailAlloc_334_, 10, v_instanceTypedMVars_320_);
lean_ctor_set(v_reuseFailAlloc_334_, 11, v_synthNormMemo_321_);
v___x_328_ = v_reuseFailAlloc_334_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_330_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_328_);
v___x_330_ = v___x_308_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_cache_303_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_zetaDeltaFVarIds_304_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_postponed_305_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v_diag_306_);
v___x_330_ = v_reuseFailAlloc_333_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_st_ref_put(v___y_299_, v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_325_);
return v___x_332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg___boxed(lean_object* v_mvarId_337_, lean_object* v_val_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_337_, v_val_338_, v___y_339_);
lean_dec(v___y_339_);
return v_res_341_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_box(0);
v___x_353_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5));
v___x_354_ = l_Lean_mkConst(v___x_353_, v___x_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object* v_result_355_, lean_object* v_mvarId_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; 
lean_inc(v_mvarId_356_);
v___x_364_ = l_Lean_MVarId_getDecl(v_mvarId_356_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
if (lean_obj_tag(v___x_364_) == 0)
{
if (lean_obj_tag(v_result_355_) == 0)
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_372_; 
lean_dec_ref_known(v_result_355_, 0);
lean_dec(v_mvarId_356_);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_372_ == 0)
{
lean_object* v_unused_373_; 
v_unused_373_ = lean_ctor_get(v___x_364_, 0);
lean_dec(v_unused_373_);
v___x_366_ = v___x_364_;
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
else
{
lean_dec(v___x_364_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_372_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_368_ = lean_box(0);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 0, v___x_368_);
v___x_370_ = v___x_366_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v_e_x27_375_; lean_object* v_proof_376_; lean_object* v_userName_377_; lean_object* v_type_378_; lean_object* v___x_379_; 
v_a_374_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_364_, 1);
v_e_x27_375_ = lean_ctor_get(v_result_355_, 0);
lean_inc_ref_n(v_e_x27_375_, 2);
v_proof_376_ = lean_ctor_get(v_result_355_, 1);
lean_inc_ref(v_proof_376_);
lean_dec_ref_known(v_result_355_, 2);
v_userName_377_ = lean_ctor_get(v_a_374_, 0);
lean_inc(v_userName_377_);
v_type_378_ = lean_ctor_get(v_a_374_, 2);
lean_inc_ref(v_type_378_);
lean_dec(v_a_374_);
v___x_379_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_e_x27_375_, v_userName_377_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v_a_380_; lean_object* v___x_381_; 
v_a_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_a_380_);
lean_dec_ref_known(v___x_379_, 1);
lean_inc_ref(v_type_378_);
v___x_381_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_378_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_410_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v___x_381_, 1);
v___x_383_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2));
v___x_384_ = lean_box(0);
v___x_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_385_, 0, v_a_382_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = l_Lean_mkConst(v___x_383_, v___x_385_);
lean_inc(v_a_380_);
lean_inc_ref(v_e_x27_375_);
v___x_387_ = l_Lean_mkApp4(v___x_386_, v_type_378_, v_e_x27_375_, v_proof_376_, v_a_380_);
v___x_388_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_356_, v___x_387_, v_a_360_);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_388_, 0);
lean_dec(v_unused_411_);
v___x_390_ = v___x_388_;
v_isShared_391_ = v_isSharedCheck_410_;
goto v_resetjp_389_;
}
else
{
lean_dec(v___x_388_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_410_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
uint8_t v___x_392_; 
v___x_392_ = l_Lean_Expr_isTrue(v_e_x27_375_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_393_ = l_Lean_Expr_mvarId_x21(v_a_380_);
lean_dec(v_a_380_);
v___x_394_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_394_);
v___x_396_ = v___x_390_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_408_; 
lean_del_object(v___x_390_);
v___x_398_ = l_Lean_Expr_mvarId_x21(v_a_380_);
lean_dec(v_a_380_);
v___x_399_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6, &l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6_once, _init_l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6);
v___x_400_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v___x_398_, v___x_399_, v_a_360_);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_400_, 0);
lean_dec(v_unused_409_);
v___x_402_ = v___x_400_;
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
else
{
lean_dec(v___x_400_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_408_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_box(1);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_404_);
v___x_406_ = v___x_402_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
lean_dec(v_a_380_);
lean_dec_ref(v_type_378_);
lean_dec_ref(v_proof_376_);
lean_dec_ref(v_e_x27_375_);
lean_dec(v_mvarId_356_);
v_a_412_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_381_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_381_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
lean_dec_ref(v_type_378_);
lean_dec_ref(v_proof_376_);
lean_dec_ref(v_e_x27_375_);
lean_dec(v_mvarId_356_);
v_a_420_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_379_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_379_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec(v_mvarId_356_);
lean_dec_ref(v_result_355_);
v_a_428_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_364_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_364_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___boxed(lean_object* v_result_436_, lean_object* v_mvarId_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_result_436_, v_mvarId_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0(lean_object* v_mvarId_446_, lean_object* v_val_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_446_, v_val_447_, v___y_451_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___boxed(lean_object* v_mvarId_456_, lean_object* v_val_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0(v_mvarId_456_, v_val_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0(lean_object* v_00_u03b2_466_, lean_object* v_x_467_, lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(v_x_467_, v_x_468_, v_x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_471_, lean_object* v_x_472_, size_t v_x_473_, size_t v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_472_, v_x_473_, v_x_474_, v_x_475_, v_x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
size_t v_x_3554__boxed_484_; size_t v_x_3555__boxed_485_; lean_object* v_res_486_; 
v_x_3554__boxed_484_ = lean_unbox_usize(v_x_480_);
lean_dec(v_x_480_);
v_x_3555__boxed_485_ = lean_unbox_usize(v_x_481_);
lean_dec(v_x_481_);
v_res_486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1(v_00_u03b2_478_, v_x_479_, v_x_3554__boxed_484_, v_x_3555__boxed_485_, v_x_482_, v_x_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_487_, lean_object* v_n_488_, lean_object* v_k_489_, lean_object* v_v_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(v_n_488_, v_k_489_, v_v_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_492_, size_t v_depth_493_, lean_object* v_keys_494_, lean_object* v_vals_495_, lean_object* v_heq_496_, lean_object* v_i_497_, lean_object* v_entries_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_493_, v_keys_494_, v_vals_495_, v_i_497_, v_entries_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_500_, lean_object* v_depth_501_, lean_object* v_keys_502_, lean_object* v_vals_503_, lean_object* v_heq_504_, lean_object* v_i_505_, lean_object* v_entries_506_){
_start:
{
size_t v_depth_boxed_507_; lean_object* v_res_508_; 
v_depth_boxed_507_ = lean_unbox_usize(v_depth_501_);
lean_dec(v_depth_501_);
v_res_508_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_500_, v_depth_boxed_507_, v_keys_502_, v_vals_503_, v_heq_504_, v_i_505_, v_entries_506_);
lean_dec_ref(v_vals_503_);
lean_dec_ref(v_keys_502_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_509_, lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_510_, v_x_511_, v_x_512_, v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0(lean_object* v_x_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; 
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
v___x_523_ = lean_apply_7(v_x_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, lean_box(0));
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0___boxed(lean_object* v_x_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0(v_x_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(lean_object* v_mvarId_533_, lean_object* v_x_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v___f_542_; lean_object* v___x_543_; 
lean_inc(v___y_536_);
lean_inc_ref(v___y_535_);
v___f_542_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_542_, 0, v_x_534_);
lean_closure_set(v___f_542_, 1, v___y_535_);
lean_closure_set(v___f_542_, 2, v___y_536_);
v___x_543_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_533_, v___f_542_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
if (lean_obj_tag(v___x_543_) == 0)
{
return v___x_543_;
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___boxed(lean_object* v_mvarId_552_, lean_object* v_x_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_552_, v_x_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0(lean_object* v_00_u03b1_562_, lean_object* v_mvarId_563_, lean_object* v_x_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_563_, v_x_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___boxed(lean_object* v_00_u03b1_573_, lean_object* v_mvarId_574_, lean_object* v_x_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0(v_00_u03b1_573_, v_mvarId_574_, v_x_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___lam__0(lean_object* v_mvarId_584_, lean_object* v_methods_585_, lean_object* v_config_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; 
lean_inc(v_mvarId_584_);
v___x_594_ = l_Lean_MVarId_getDecl(v_mvarId_584_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v_type_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
v_type_596_ = lean_ctor_get(v_a_595_, 2);
lean_inc_ref(v_type_596_);
lean_dec(v_a_595_);
v___x_597_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_597_, 0, v_type_596_);
v___x_598_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_597_, v_methods_585_, v_config_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v_a_599_; lean_object* v___x_600_; 
v_a_599_ = lean_ctor_get(v___x_598_, 0);
lean_inc(v_a_599_);
lean_dec_ref_known(v___x_598_, 1);
v___x_600_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_a_599_, v_mvarId_584_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_);
return v___x_600_;
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec(v_mvarId_584_);
v_a_601_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_598_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_598_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v_config_586_);
lean_dec_ref(v_methods_585_);
lean_dec(v_mvarId_584_);
v_a_609_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_594_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_594_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___lam__0___boxed(lean_object* v_mvarId_617_, lean_object* v_methods_618_, lean_object* v_config_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l_Lean_Meta_Sym_simpGoal___lam__0(v_mvarId_617_, v_methods_618_, v_config_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal(lean_object* v_mvarId_628_, lean_object* v_methods_629_, lean_object* v_config_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_){
_start:
{
lean_object* v___f_638_; lean_object* v___x_639_; 
lean_inc(v_mvarId_628_);
v___f_638_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_simpGoal___lam__0___boxed), 10, 3);
lean_closure_set(v___f_638_, 0, v_mvarId_628_);
lean_closure_set(v___f_638_, 1, v_methods_629_);
lean_closure_set(v___f_638_, 2, v_config_630_);
v___x_639_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_628_, v___f_638_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___boxed(lean_object* v_mvarId_640_, lean_object* v_methods_641_, lean_object* v_config_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_640_, v_methods_641_, v_config_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_);
lean_dec(v_a_648_);
lean_dec_ref(v_a_647_);
lean_dec(v_a_646_);
lean_dec_ref(v_a_645_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalIgnoringNoProgress(lean_object* v_mvarId_651_, lean_object* v_methods_652_, lean_object* v_config_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___x_661_; 
lean_inc(v_mvarId_651_);
v___x_661_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_651_, v_methods_652_, v_config_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
if (lean_obj_tag(v_a_662_) == 0)
{
lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_670_; 
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_670_ == 0)
{
lean_object* v_unused_671_; 
v_unused_671_ = lean_ctor_get(v___x_661_, 0);
lean_dec(v_unused_671_);
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
else
{
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_666_, 0, v_mvarId_651_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_dec(v_mvarId_651_);
return v___x_661_;
}
}
else
{
lean_dec(v_mvarId_651_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalIgnoringNoProgress___boxed(lean_object* v_mvarId_672_, lean_object* v_methods_673_, lean_object* v_config_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Meta_Sym_simpGoalIgnoringNoProgress(v_mvarId_672_, v_methods_673_, v_config_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
return v_res_682_;
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
