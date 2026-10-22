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
v___x_51_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_51_, 10, v___x_48_);
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
size_t v_x_3121__boxed_287_; size_t v_x_3122__boxed_288_; lean_object* v_res_289_; 
v_x_3121__boxed_287_ = lean_unbox_usize(v_x_283_);
lean_dec(v_x_283_);
v_x_3122__boxed_288_ = lean_unbox_usize(v_x_284_);
lean_dec(v_x_284_);
v_res_289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_282_, v_x_3121__boxed_287_, v_x_3122__boxed_288_, v_x_285_, v_x_286_);
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
lean_object* v___x_301_; lean_object* v_mctx_302_; lean_object* v_cache_303_; lean_object* v_zetaDeltaFVarIds_304_; lean_object* v_postponed_305_; lean_object* v_diag_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_335_; 
v___x_301_ = lean_st_ref_take(v___y_299_);
v_mctx_302_ = lean_ctor_get(v___x_301_, 0);
v_cache_303_ = lean_ctor_get(v___x_301_, 1);
v_zetaDeltaFVarIds_304_ = lean_ctor_get(v___x_301_, 2);
v_postponed_305_ = lean_ctor_get(v___x_301_, 3);
v_diag_306_ = lean_ctor_get(v___x_301_, 4);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_335_ == 0)
{
v___x_308_ = v___x_301_;
v_isShared_309_ = v_isSharedCheck_335_;
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
v_isShared_309_ = v_isSharedCheck_335_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_depth_310_; lean_object* v_levelAssignDepth_311_; lean_object* v_lmvarCounter_312_; lean_object* v_mvarCounter_313_; lean_object* v_lDecls_314_; lean_object* v_decls_315_; lean_object* v_userNames_316_; lean_object* v_lAssignment_317_; lean_object* v_eAssignment_318_; lean_object* v_dAssignment_319_; lean_object* v_synthNormMemo_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_334_; 
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
v_synthNormMemo_320_ = lean_ctor_get(v_mctx_302_, 10);
v_isSharedCheck_334_ = !lean_is_exclusive(v_mctx_302_);
if (v_isSharedCheck_334_ == 0)
{
v___x_322_ = v_mctx_302_;
v_isShared_323_ = v_isSharedCheck_334_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_synthNormMemo_320_);
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
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_334_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_324_ = lean_box(0);
v___x_325_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(v_eAssignment_318_, v_mvarId_297_, v_val_298_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 8, v___x_325_);
v___x_327_ = v___x_322_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_depth_310_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_levelAssignDepth_311_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_lmvarCounter_312_);
lean_ctor_set(v_reuseFailAlloc_333_, 3, v_mvarCounter_313_);
lean_ctor_set(v_reuseFailAlloc_333_, 4, v_lDecls_314_);
lean_ctor_set(v_reuseFailAlloc_333_, 5, v_decls_315_);
lean_ctor_set(v_reuseFailAlloc_333_, 6, v_userNames_316_);
lean_ctor_set(v_reuseFailAlloc_333_, 7, v_lAssignment_317_);
lean_ctor_set(v_reuseFailAlloc_333_, 8, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_333_, 9, v_dAssignment_319_);
lean_ctor_set(v_reuseFailAlloc_333_, 10, v_synthNormMemo_320_);
v___x_327_ = v_reuseFailAlloc_333_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_329_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_327_);
v___x_329_ = v___x_308_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_327_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_cache_303_);
lean_ctor_set(v_reuseFailAlloc_332_, 2, v_zetaDeltaFVarIds_304_);
lean_ctor_set(v_reuseFailAlloc_332_, 3, v_postponed_305_);
lean_ctor_set(v_reuseFailAlloc_332_, 4, v_diag_306_);
v___x_329_ = v_reuseFailAlloc_332_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_st_ref_put(v___y_299_, v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_324_);
return v___x_331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg___boxed(lean_object* v_mvarId_336_, lean_object* v_val_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_336_, v_val_337_, v___y_338_);
lean_dec(v___y_338_);
return v_res_340_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = lean_box(0);
v___x_352_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__5));
v___x_353_ = l_Lean_mkConst(v___x_352_, v___x_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(lean_object* v_result_354_, lean_object* v_mvarId_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_){
_start:
{
lean_object* v___x_363_; 
lean_inc(v_mvarId_355_);
v___x_363_ = l_Lean_MVarId_getDecl(v_mvarId_355_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_363_) == 0)
{
if (lean_obj_tag(v_result_354_) == 0)
{
lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref_known(v_result_354_, 0);
lean_dec(v_mvarId_355_);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; 
v_unused_372_ = lean_ctor_get(v___x_363_, 0);
lean_dec(v_unused_372_);
v___x_365_ = v___x_363_;
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
else
{
lean_dec(v___x_363_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_371_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_box(0);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_367_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
else
{
lean_object* v_a_373_; lean_object* v_e_x27_374_; lean_object* v_proof_375_; lean_object* v_userName_376_; lean_object* v_type_377_; lean_object* v___x_378_; 
v_a_373_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_363_, 1);
v_e_x27_374_ = lean_ctor_get(v_result_354_, 0);
lean_inc_ref_n(v_e_x27_374_, 2);
v_proof_375_ = lean_ctor_get(v_result_354_, 1);
lean_inc_ref(v_proof_375_);
lean_dec_ref_known(v_result_354_, 2);
v_userName_376_ = lean_ctor_get(v_a_373_, 0);
lean_inc(v_userName_376_);
v_type_377_ = lean_ctor_get(v_a_373_, 2);
lean_inc_ref(v_type_377_);
lean_dec(v_a_373_);
v___x_378_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_e_x27_374_, v_userName_376_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_380_; 
v_a_379_ = lean_ctor_get(v___x_378_, 0);
lean_inc(v_a_379_);
lean_dec_ref_known(v___x_378_, 1);
lean_inc_ref(v_type_377_);
v___x_380_ = l_Lean_Meta_Sym_getLevel___redArg(v_type_377_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_409_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
lean_dec_ref_known(v___x_380_, 1);
v___x_382_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__2));
v___x_383_ = lean_box(0);
v___x_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_384_, 0, v_a_381_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = l_Lean_mkConst(v___x_382_, v___x_384_);
lean_inc(v_a_379_);
lean_inc_ref(v_e_x27_374_);
v___x_386_ = l_Lean_mkApp4(v___x_385_, v_type_377_, v_e_x27_374_, v_proof_375_, v_a_379_);
v___x_387_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_355_, v___x_386_, v_a_359_);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_387_, 0);
lean_dec(v_unused_410_);
v___x_389_ = v___x_387_;
v_isShared_390_ = v_isSharedCheck_409_;
goto v_resetjp_388_;
}
else
{
lean_dec(v___x_387_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_409_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint8_t v___x_391_; 
v___x_391_ = l_Lean_Expr_isTrue(v_e_x27_374_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_392_ = l_Lean_Expr_mvarId_x21(v_a_379_);
lean_dec(v_a_379_);
v___x_393_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_393_);
v___x_395_ = v___x_389_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_407_; 
lean_del_object(v___x_389_);
v___x_397_ = l_Lean_Expr_mvarId_x21(v_a_379_);
lean_dec(v_a_379_);
v___x_398_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6, &l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6_once, _init_l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___closed__6);
v___x_399_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v___x_397_, v___x_398_, v_a_359_);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v___x_399_, 0);
lean_dec(v_unused_408_);
v___x_401_ = v___x_399_;
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
else
{
lean_dec(v___x_399_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_407_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_403_ = lean_box(1);
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_403_);
v___x_405_ = v___x_401_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_a_379_);
lean_dec_ref(v_type_377_);
lean_dec_ref(v_proof_375_);
lean_dec_ref(v_e_x27_374_);
lean_dec(v_mvarId_355_);
v_a_411_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_380_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_380_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_type_377_);
lean_dec_ref(v_proof_375_);
lean_dec_ref(v_e_x27_374_);
lean_dec(v_mvarId_355_);
v_a_419_ = lean_ctor_get(v___x_378_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_378_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_378_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec(v_mvarId_355_);
lean_dec_ref(v_result_354_);
v_a_427_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_363_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_363_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult___boxed(lean_object* v_result_435_, lean_object* v_mvarId_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_result_435_, v_mvarId_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0(lean_object* v_mvarId_445_, lean_object* v_val_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___redArg(v_mvarId_445_, v_val_446_, v___y_450_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0___boxed(lean_object* v_mvarId_455_, lean_object* v_val_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0(v_mvarId_455_, v_val_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0(lean_object* v_00_u03b2_465_, lean_object* v_x_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0___redArg(v_x_466_, v_x_467_, v_x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_470_, lean_object* v_x_471_, size_t v_x_472_, size_t v_x_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___redArg(v_x_471_, v_x_472_, v_x_473_, v_x_474_, v_x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
size_t v_x_3550__boxed_483_; size_t v_x_3551__boxed_484_; lean_object* v_res_485_; 
v_x_3550__boxed_483_ = lean_unbox_usize(v_x_479_);
lean_dec(v_x_479_);
v_x_3551__boxed_484_ = lean_unbox_usize(v_x_480_);
lean_dec(v_x_480_);
v_res_485_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1(v_00_u03b2_477_, v_x_478_, v_x_3550__boxed_483_, v_x_3551__boxed_484_, v_x_481_, v_x_482_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_486_, lean_object* v_n_487_, lean_object* v_k_488_, lean_object* v_v_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2___redArg(v_n_487_, v_k_488_, v_v_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_491_, size_t v_depth_492_, lean_object* v_keys_493_, lean_object* v_vals_494_, lean_object* v_heq_495_, lean_object* v_i_496_, lean_object* v_entries_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_492_, v_keys_493_, v_vals_494_, v_i_496_, v_entries_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_499_, lean_object* v_depth_500_, lean_object* v_keys_501_, lean_object* v_vals_502_, lean_object* v_heq_503_, lean_object* v_i_504_, lean_object* v_entries_505_){
_start:
{
size_t v_depth_boxed_506_; lean_object* v_res_507_; 
v_depth_boxed_506_ = lean_unbox_usize(v_depth_500_);
lean_dec(v_depth_500_);
v_res_507_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_499_, v_depth_boxed_506_, v_keys_501_, v_vals_502_, v_heq_503_, v_i_504_, v_entries_505_);
lean_dec_ref(v_vals_502_);
lean_dec_ref(v_keys_501_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_, lean_object* v_x_512_){
_start:
{
lean_object* v___x_513_; 
v___x_513_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_Simp_Result_toSimpGoalResult_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_509_, v_x_510_, v_x_511_, v_x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0(lean_object* v_x_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
lean_inc(v___y_516_);
lean_inc_ref(v___y_515_);
v___x_522_ = lean_apply_7(v_x_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, lean_box(0));
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0___boxed(lean_object* v_x_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0(v_x_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(lean_object* v_mvarId_532_, lean_object* v_x_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___f_541_; lean_object* v___x_542_; 
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
v___f_541_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_541_, 0, v_x_533_);
lean_closure_set(v___f_541_, 1, v___y_534_);
lean_closure_set(v___f_541_, 2, v___y_535_);
v___x_542_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_532_, v___f_541_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
if (lean_obj_tag(v___x_542_) == 0)
{
return v___x_542_;
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg___boxed(lean_object* v_mvarId_551_, lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_551_, v_x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0(lean_object* v_00_u03b1_561_, lean_object* v_mvarId_562_, lean_object* v_x_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_562_, v_x_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___boxed(lean_object* v_00_u03b1_572_, lean_object* v_mvarId_573_, lean_object* v_x_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0(v_00_u03b1_572_, v_mvarId_573_, v_x_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___lam__0(lean_object* v_mvarId_583_, lean_object* v_methods_584_, lean_object* v_config_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_){
_start:
{
lean_object* v___x_593_; 
lean_inc(v_mvarId_583_);
v___x_593_ = l_Lean_MVarId_getDecl(v_mvarId_583_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v_type_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v_type_595_ = lean_ctor_get(v_a_594_, 2);
lean_inc_ref(v_type_595_);
lean_dec(v_a_594_);
v___x_596_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_596_, 0, v_type_595_);
v___x_597_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_596_, v_methods_584_, v_config_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_599_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = l_Lean_Meta_Sym_Simp_Result_toSimpGoalResult(v_a_598_, v_mvarId_583_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
return v___x_599_;
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v_mvarId_583_);
v_a_600_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_597_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_597_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
lean_dec_ref(v_config_585_);
lean_dec_ref(v_methods_584_);
lean_dec(v_mvarId_583_);
v_a_608_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_593_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_593_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___lam__0___boxed(lean_object* v_mvarId_616_, lean_object* v_methods_617_, lean_object* v_config_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Lean_Meta_Sym_simpGoal___lam__0(v_mvarId_616_, v_methods_617_, v_config_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal(lean_object* v_mvarId_627_, lean_object* v_methods_628_, lean_object* v_config_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___f_637_; lean_object* v___x_638_; 
lean_inc(v_mvarId_627_);
v___f_637_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_simpGoal___lam__0___boxed), 10, 3);
lean_closure_set(v___f_637_, 0, v_mvarId_627_);
lean_closure_set(v___f_637_, 1, v_methods_628_);
lean_closure_set(v___f_637_, 2, v_config_629_);
v___x_638_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_simpGoal_spec__0___redArg(v_mvarId_627_, v___f_637_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoal___boxed(lean_object* v_mvarId_639_, lean_object* v_methods_640_, lean_object* v_config_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_639_, v_methods_640_, v_config_641_, v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
lean_dec(v_a_645_);
lean_dec_ref(v_a_644_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalIgnoringNoProgress(lean_object* v_mvarId_650_, lean_object* v_methods_651_, lean_object* v_config_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v___x_660_; 
lean_inc(v_mvarId_650_);
v___x_660_ = l_Lean_Meta_Sym_simpGoal(v_mvarId_650_, v_methods_651_, v_config_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
if (lean_obj_tag(v_a_661_) == 0)
{
lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_669_; 
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v___x_660_, 0);
lean_dec(v_unused_670_);
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
else
{
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_665_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_665_, 0, v_mvarId_650_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_665_);
v___x_667_ = v___x_663_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_dec(v_mvarId_650_);
return v___x_660_;
}
}
else
{
lean_dec(v_mvarId_650_);
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_simpGoalIgnoringNoProgress___boxed(lean_object* v_mvarId_671_, lean_object* v_methods_672_, lean_object* v_config_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_Sym_simpGoalIgnoringNoProgress(v_mvarId_671_, v_methods_672_, v_config_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec_ref(v_a_674_);
return v_res_681_;
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
