// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Basic
// Imports: public import Std.Tactic.Do.Syntax public import Lean.Elab.Tactic.Do.ProofMode.MGoal
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_level_mvars(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(lean_object*);
lean_object* l_Lean_MVarId_setType___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "PropAsSPredTautology"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__5_value),LEAN_SCALAR_PTR_LITERAL(48, 191, 216, 96, 0, 209, 179, 40)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "start_entails"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 48, 44, 122, 88, 53, 63, 251)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value),LEAN_SCALAR_PTR_LITERAL(21, 12, 10, 60, 47, 13, 234, 221)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__8_value),LEAN_SCALAR_PTR_LITERAL(47, 181, 74, 89, 75, 246, 200, 35)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "The goal type of `"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` is not a proposition. It has type `"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mstart"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(12, 72, 234, 250, 239, 149, 139, 165)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMStart"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(74, 124, 237, 138, 104, 184, 13, 121)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not in proof mode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mstop"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 209, 80, 25, 253, 26, 68, 170)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabMStop"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 207, 43, 105, 62, 50, 202, 255)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(lean_object* v_l_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_mctx_5_; lean_object* v___x_6_; lean_object* v_fst_7_; lean_object* v_snd_8_; lean_object* v___x_9_; lean_object* v_cache_10_; lean_object* v_zetaDeltaFVarIds_11_; lean_object* v_postponed_12_; lean_object* v_diag_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_22_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_mctx_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref(v_mctx_5_);
lean_dec(v___x_4_);
v___x_6_ = lean_instantiate_level_mvars(v_mctx_5_, v_l_1_);
v_fst_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_fst_7_);
v_snd_8_ = lean_ctor_get(v___x_6_, 1);
lean_inc(v_snd_8_);
lean_dec_ref(v___x_6_);
v___x_9_ = lean_st_ref_take(v___y_2_);
v_cache_10_ = lean_ctor_get(v___x_9_, 1);
v_zetaDeltaFVarIds_11_ = lean_ctor_get(v___x_9_, 2);
v_postponed_12_ = lean_ctor_get(v___x_9_, 3);
v_diag_13_ = lean_ctor_get(v___x_9_, 4);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_22_ == 0)
{
lean_object* v_unused_23_; 
v_unused_23_ = lean_ctor_get(v___x_9_, 0);
lean_dec(v_unused_23_);
v___x_15_ = v___x_9_;
v_isShared_16_ = v_isSharedCheck_22_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_diag_13_);
lean_inc(v_postponed_12_);
lean_inc(v_zetaDeltaFVarIds_11_);
lean_inc(v_cache_10_);
lean_dec(v___x_9_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_22_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v_fst_7_);
v___x_18_ = v___x_15_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_fst_7_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v_cache_10_);
lean_ctor_set(v_reuseFailAlloc_21_, 2, v_zetaDeltaFVarIds_11_);
lean_ctor_set(v_reuseFailAlloc_21_, 3, v_postponed_12_);
lean_ctor_set(v_reuseFailAlloc_21_, 4, v_diag_13_);
v___x_18_ = v_reuseFailAlloc_21_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_st_ref_set(v___y_2_, v___x_18_);
v___x_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_20_, 0, v_snd_8_);
return v___x_20_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg___boxed(lean_object* v_l_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(v_l_24_, v___y_25_);
lean_dec(v___y_25_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0(lean_object* v_l_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(v_l_28_, v___y_30_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___boxed(lean_object* v_l_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0(v_l_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(lean_object* v_e_42_, lean_object* v___y_43_){
_start:
{
uint8_t v___x_45_; 
v___x_45_ = l_Lean_Expr_hasMVar(v_e_42_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
v___x_46_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_46_, 0, v_e_42_);
return v___x_46_;
}
else
{
lean_object* v___x_47_; lean_object* v_mctx_48_; lean_object* v___x_49_; lean_object* v_fst_50_; lean_object* v_snd_51_; lean_object* v___x_52_; lean_object* v_cache_53_; lean_object* v_zetaDeltaFVarIds_54_; lean_object* v_postponed_55_; lean_object* v_diag_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_65_; 
v___x_47_ = lean_st_ref_get(v___y_43_);
v_mctx_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc_ref(v_mctx_48_);
lean_dec(v___x_47_);
v___x_49_ = l_Lean_instantiateMVarsCore(v_mctx_48_, v_e_42_);
v_fst_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc(v_fst_50_);
v_snd_51_ = lean_ctor_get(v___x_49_, 1);
lean_inc(v_snd_51_);
lean_dec_ref(v___x_49_);
v___x_52_ = lean_st_ref_take(v___y_43_);
v_cache_53_ = lean_ctor_get(v___x_52_, 1);
v_zetaDeltaFVarIds_54_ = lean_ctor_get(v___x_52_, 2);
v_postponed_55_ = lean_ctor_get(v___x_52_, 3);
v_diag_56_ = lean_ctor_get(v___x_52_, 4);
v_isSharedCheck_65_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_65_ == 0)
{
lean_object* v_unused_66_; 
v_unused_66_ = lean_ctor_get(v___x_52_, 0);
lean_dec(v_unused_66_);
v___x_58_ = v___x_52_;
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_diag_56_);
lean_inc(v_postponed_55_);
lean_inc(v_zetaDeltaFVarIds_54_);
lean_inc(v_cache_53_);
lean_dec(v___x_52_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_65_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v_snd_51_);
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_snd_51_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_cache_53_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_zetaDeltaFVarIds_54_);
lean_ctor_set(v_reuseFailAlloc_64_, 3, v_postponed_55_);
lean_ctor_set(v_reuseFailAlloc_64_, 4, v_diag_56_);
v___x_61_ = v_reuseFailAlloc_64_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_st_ref_set(v___y_43_, v___x_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v_fst_50_);
return v___x_63_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg___boxed(lean_object* v_e_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(v_e_67_, v___y_68_);
lean_dec(v___y_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1(lean_object* v_e_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(v_e_71_, v___y_73_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___boxed(lean_object* v_e_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1(v_e_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart(lean_object* v_goal_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_goal_109_);
if (lean_obj_tag(v___x_115_) == 1)
{
lean_object* v_val_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_125_; 
lean_dec_ref(v_goal_109_);
v_val_116_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_125_ == 0)
{
v___x_118_ = v___x_115_;
v_isShared_119_ = v_isSharedCheck_125_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_val_116_);
lean_dec(v___x_115_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_125_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_120_ = lean_box(0);
v___x_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_121_, 0, v_val_116_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 0);
lean_ctor_set(v___x_118_, 0, v___x_121_);
v___x_123_ = v___x_118_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
else
{
lean_object* v___x_126_; 
lean_dec(v___x_115_);
v___x_126_ = l_Lean_Meta_mkFreshLevelMVar(v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_a_127_);
lean_dec_ref(v___x_126_);
lean_inc(v_a_127_);
v___x_128_ = l_Lean_Elab_Tactic_Do_ProofMode_TypeList_mkType(v_a_127_);
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
v___x_130_ = 0;
v___x_131_ = lean_box(0);
v___x_132_ = l_Lean_Meta_mkFreshExprMVar(v___x_129_, v___x_130_, v___x_131_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_a_133_);
lean_dec_ref(v___x_132_);
v___x_134_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3));
v___x_135_ = lean_box(0);
lean_inc(v_a_127_);
v___x_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_136_, 0, v_a_127_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
lean_inc_ref(v___x_136_);
v___x_137_ = l_Lean_mkConst(v___x_134_, v___x_136_);
lean_inc(v_a_133_);
v___x_138_ = l_Lean_Expr_app___override(v___x_137_, v_a_133_);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
v___x_140_ = l_Lean_Meta_mkFreshExprMVar(v___x_139_, v___x_130_, v___x_131_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref(v___x_140_);
v___x_142_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6));
v___x_143_ = l_Lean_mkConst(v___x_142_, v___x_136_);
lean_inc(v_a_141_);
lean_inc(v_a_133_);
lean_inc_ref(v_goal_109_);
v___x_144_ = l_Lean_mkApp3(v___x_143_, v_goal_109_, v_a_133_, v_a_141_);
v___x_145_ = lean_box(0);
v___x_146_ = l_Lean_Meta_synthInstance(v___x_144_, v___x_145_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_148_; lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_172_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
lean_inc(v_a_147_);
lean_dec_ref(v___x_146_);
v___x_148_ = l_Lean_instantiateLevelMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__0___redArg(v_a_127_, v_a_111_);
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_172_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_172_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_172_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_171_; 
v___x_153_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__9));
lean_inc(v_a_149_);
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v_a_149_);
lean_ctor_set(v___x_154_, 1, v___x_135_);
v___x_155_ = l_Lean_mkConst(v___x_153_, v___x_154_);
lean_inc(v_a_141_);
lean_inc(v_a_133_);
v___x_156_ = l_Lean_mkApp4(v___x_155_, v_a_133_, v_a_141_, v_goal_109_, v_a_147_);
v___x_157_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(v_a_141_, v_a_111_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_171_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_171_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_171_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
lean_inc(v_a_133_);
lean_inc(v_a_149_);
v___x_162_ = l_Lean_Elab_Tactic_Do_ProofMode_emptyHyp(v_a_149_, v_a_133_);
v___x_163_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_163_, 0, v_a_149_);
lean_ctor_set(v___x_163_, 1, v_a_133_);
lean_ctor_set(v___x_163_, 2, v___x_162_);
lean_ctor_set(v___x_163_, 3, v_a_158_);
if (v_isShared_152_ == 0)
{
lean_ctor_set_tag(v___x_151_, 1);
lean_ctor_set(v___x_151_, 0, v___x_156_);
v___x_165_ = v___x_151_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_156_);
v___x_165_ = v_reuseFailAlloc_170_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_163_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_166_);
v___x_168_ = v___x_160_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec(v_a_141_);
lean_dec(v_a_133_);
lean_dec(v_a_127_);
lean_dec_ref(v_goal_109_);
v_a_173_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_146_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_146_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec_ref(v___x_136_);
lean_dec(v_a_133_);
lean_dec(v_a_127_);
lean_dec_ref(v_goal_109_);
v_a_181_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_140_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_140_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec(v_a_127_);
lean_dec_ref(v_goal_109_);
v_a_189_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_132_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_132_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v_goal_109_);
v_a_197_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_126_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_126_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStart___boxed(lean_object* v_goal_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_Elab_Tactic_Do_ProofMode_mStart(v_goal_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(lean_object* v_mvarId_212_, lean_object* v_x_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_212_, v_x_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v_a_228_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_219_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_219_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg___boxed(lean_object* v_mvarId_236_, lean_object* v_x_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(v_mvarId_236_, v_x_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2(lean_object* v_00_u03b1_244_, lean_object* v_mvarId_245_, lean_object* v_x_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(v_mvarId_245_, v_x_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___boxed(lean_object* v_00_u03b1_253_, lean_object* v_mvarId_254_, lean_object* v_x_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2(v_00_u03b1_253_, v_mvarId_254_, v_x_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
lean_object* v_ks_266_; lean_object* v_vs_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_291_; 
v_ks_266_ = lean_ctor_get(v_x_262_, 0);
v_vs_267_ = lean_ctor_get(v_x_262_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_262_);
if (v_isSharedCheck_291_ == 0)
{
v___x_269_ = v_x_262_;
v_isShared_270_ = v_isSharedCheck_291_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_vs_267_);
lean_inc(v_ks_266_);
lean_dec(v_x_262_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_291_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_array_get_size(v_ks_266_);
v___x_272_ = lean_nat_dec_lt(v_x_263_, v___x_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec(v_x_263_);
v___x_273_ = lean_array_push(v_ks_266_, v_x_264_);
v___x_274_ = lean_array_push(v_vs_267_, v_x_265_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_274_);
lean_ctor_set(v___x_269_, 0, v___x_273_);
v___x_276_ = v___x_269_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
else
{
lean_object* v_k_x27_278_; uint8_t v___x_279_; 
v_k_x27_278_ = lean_array_fget_borrowed(v_ks_266_, v_x_263_);
v___x_279_ = l_Lean_instBEqMVarId_beq(v_x_264_, v_k_x27_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_281_; 
if (v_isShared_270_ == 0)
{
v___x_281_ = v___x_269_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_ks_266_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_vs_267_);
v___x_281_ = v_reuseFailAlloc_285_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_add(v_x_263_, v___x_282_);
lean_dec(v_x_263_);
v_x_262_ = v___x_281_;
v_x_263_ = v___x_283_;
goto _start;
}
}
else
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_286_ = lean_array_fset(v_ks_266_, v_x_263_, v_x_264_);
v___x_287_ = lean_array_fset(v_vs_267_, v_x_263_, v_x_265_);
lean_dec(v_x_263_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v___x_287_);
lean_ctor_set(v___x_269_, 0, v___x_286_);
v___x_289_ = v___x_269_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_286_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_n_292_, lean_object* v_k_293_, lean_object* v_v_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = lean_unsigned_to_nat(0u);
v___x_296_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_n_292_, v___x_295_, v_k_293_, v_v_294_);
return v___x_296_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; 
v___x_297_ = ((size_t)5ULL);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_shift_left(v___x_298_, v___x_297_);
return v___x_299_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; 
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_302_ = lean_usize_sub(v___x_301_, v___x_300_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(lean_object* v_x_304_, size_t v_x_305_, size_t v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_object* v_es_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; lean_object* v_j_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v_es_309_ = lean_ctor_get(v_x_304_, 0);
v___x_310_ = ((size_t)5ULL);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_313_ = lean_usize_land(v_x_305_, v___x_312_);
v_j_314_ = lean_usize_to_nat(v___x_313_);
v___x_315_ = lean_array_get_size(v_es_309_);
v___x_316_ = lean_nat_dec_lt(v_j_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_dec(v_j_314_);
lean_dec(v_x_308_);
lean_dec(v_x_307_);
return v_x_304_;
}
else
{
lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_353_; 
lean_inc_ref(v_es_309_);
v_isSharedCheck_353_ = !lean_is_exclusive(v_x_304_);
if (v_isSharedCheck_353_ == 0)
{
lean_object* v_unused_354_; 
v_unused_354_ = lean_ctor_get(v_x_304_, 0);
lean_dec(v_unused_354_);
v___x_318_ = v_x_304_;
v_isShared_319_ = v_isSharedCheck_353_;
goto v_resetjp_317_;
}
else
{
lean_dec(v_x_304_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_353_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v_v_320_; lean_object* v___x_321_; lean_object* v_xs_x27_322_; lean_object* v___y_324_; 
v_v_320_ = lean_array_fget(v_es_309_, v_j_314_);
v___x_321_ = lean_box(0);
v_xs_x27_322_ = lean_array_fset(v_es_309_, v_j_314_, v___x_321_);
switch(lean_obj_tag(v_v_320_))
{
case 0:
{
lean_object* v_key_329_; lean_object* v_val_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_340_; 
v_key_329_ = lean_ctor_get(v_v_320_, 0);
v_val_330_ = lean_ctor_get(v_v_320_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_v_320_);
if (v_isSharedCheck_340_ == 0)
{
v___x_332_ = v_v_320_;
v_isShared_333_ = v_isSharedCheck_340_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_val_330_);
lean_inc(v_key_329_);
lean_dec(v_v_320_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_340_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
uint8_t v___x_334_; 
v___x_334_ = l_Lean_instBEqMVarId_beq(v_x_307_, v_key_329_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_del_object(v___x_332_);
v___x_335_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_329_, v_val_330_, v_x_307_, v_x_308_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
v___y_324_ = v___x_336_;
goto v___jp_323_;
}
else
{
lean_object* v___x_338_; 
lean_dec(v_val_330_);
lean_dec(v_key_329_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v_x_308_);
lean_ctor_set(v___x_332_, 0, v_x_307_);
v___x_338_ = v___x_332_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_x_307_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_x_308_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
v___y_324_ = v___x_338_;
goto v___jp_323_;
}
}
}
}
case 1:
{
lean_object* v_node_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_351_; 
v_node_341_ = lean_ctor_get(v_v_320_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v_v_320_);
if (v_isSharedCheck_351_ == 0)
{
v___x_343_ = v_v_320_;
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_node_341_);
lean_dec(v_v_320_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
size_t v___x_345_; size_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_345_ = lean_usize_shift_right(v_x_305_, v___x_310_);
v___x_346_ = lean_usize_add(v_x_306_, v___x_311_);
v___x_347_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_node_341_, v___x_345_, v___x_346_, v_x_307_, v_x_308_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_347_);
v___x_349_ = v___x_343_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
v___y_324_ = v___x_349_;
goto v___jp_323_;
}
}
}
default: 
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v_x_307_);
lean_ctor_set(v___x_352_, 1, v_x_308_);
v___y_324_ = v___x_352_;
goto v___jp_323_;
}
}
v___jp_323_:
{
lean_object* v___x_325_; lean_object* v___x_327_; 
v___x_325_ = lean_array_fset(v_xs_x27_322_, v_j_314_, v___y_324_);
lean_dec(v_j_314_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_325_);
v___x_327_ = v___x_318_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
else
{
lean_object* v_ks_355_; lean_object* v_vs_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_376_; 
v_ks_355_ = lean_ctor_get(v_x_304_, 0);
v_vs_356_ = lean_ctor_get(v_x_304_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_x_304_);
if (v_isSharedCheck_376_ == 0)
{
v___x_358_ = v_x_304_;
v_isShared_359_ = v_isSharedCheck_376_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_vs_356_);
lean_inc(v_ks_355_);
lean_dec(v_x_304_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_376_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_ks_355_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_vs_356_);
v___x_361_ = v_reuseFailAlloc_375_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v_newNode_362_; uint8_t v___y_364_; size_t v___x_370_; uint8_t v___x_371_; 
v_newNode_362_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5___redArg(v___x_361_, v_x_307_, v_x_308_);
v___x_370_ = ((size_t)7ULL);
v___x_371_ = lean_usize_dec_le(v___x_370_, v_x_306_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v___x_372_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_362_);
v___x_373_ = lean_unsigned_to_nat(4u);
v___x_374_ = lean_nat_dec_lt(v___x_372_, v___x_373_);
lean_dec(v___x_372_);
v___y_364_ = v___x_374_;
goto v___jp_363_;
}
else
{
v___y_364_ = v___x_371_;
goto v___jp_363_;
}
v___jp_363_:
{
if (v___y_364_ == 0)
{
lean_object* v_ks_365_; lean_object* v_vs_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v_ks_365_ = lean_ctor_get(v_newNode_362_, 0);
lean_inc_ref(v_ks_365_);
v_vs_366_ = lean_ctor_get(v_newNode_362_, 1);
lean_inc_ref(v_vs_366_);
lean_dec_ref(v_newNode_362_);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_369_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_x_306_, v_ks_365_, v_vs_366_, v___x_367_, v___x_368_);
lean_dec_ref(v_vs_366_);
lean_dec_ref(v_ks_365_);
return v___x_369_;
}
else
{
return v_newNode_362_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(size_t v_depth_377_, lean_object* v_keys_378_, lean_object* v_vals_379_, lean_object* v_i_380_, lean_object* v_entries_381_){
_start:
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = lean_array_get_size(v_keys_378_);
v___x_383_ = lean_nat_dec_lt(v_i_380_, v___x_382_);
if (v___x_383_ == 0)
{
lean_dec(v_i_380_);
return v_entries_381_;
}
else
{
lean_object* v_k_384_; lean_object* v_v_385_; uint64_t v___x_386_; size_t v_h_387_; size_t v___x_388_; lean_object* v___x_389_; size_t v___x_390_; size_t v___x_391_; size_t v___x_392_; size_t v_h_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_k_384_ = lean_array_fget_borrowed(v_keys_378_, v_i_380_);
v_v_385_ = lean_array_fget_borrowed(v_vals_379_, v_i_380_);
v___x_386_ = l_Lean_instHashableMVarId_hash(v_k_384_);
v_h_387_ = lean_uint64_to_usize(v___x_386_);
v___x_388_ = ((size_t)5ULL);
v___x_389_ = lean_unsigned_to_nat(1u);
v___x_390_ = ((size_t)1ULL);
v___x_391_ = lean_usize_sub(v_depth_377_, v___x_390_);
v___x_392_ = lean_usize_mul(v___x_388_, v___x_391_);
v_h_393_ = lean_usize_shift_right(v_h_387_, v___x_392_);
v___x_394_ = lean_nat_add(v_i_380_, v___x_389_);
lean_dec(v_i_380_);
lean_inc(v_v_385_);
lean_inc(v_k_384_);
v___x_395_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_entries_381_, v_h_393_, v_depth_377_, v_k_384_, v_v_385_);
v_i_380_ = v___x_394_;
v_entries_381_ = v___x_395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_depth_397_, lean_object* v_keys_398_, lean_object* v_vals_399_, lean_object* v_i_400_, lean_object* v_entries_401_){
_start:
{
size_t v_depth_boxed_402_; lean_object* v_res_403_; 
v_depth_boxed_402_ = lean_unbox_usize(v_depth_397_);
lean_dec(v_depth_397_);
v_res_403_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_boxed_402_, v_keys_398_, v_vals_399_, v_i_400_, v_entries_401_);
lean_dec_ref(v_vals_399_);
lean_dec_ref(v_keys_398_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_, lean_object* v_x_408_){
_start:
{
size_t v_x_3522__boxed_409_; size_t v_x_3523__boxed_410_; lean_object* v_res_411_; 
v_x_3522__boxed_409_ = lean_unbox_usize(v_x_405_);
lean_dec(v_x_405_);
v_x_3523__boxed_410_ = lean_unbox_usize(v_x_406_);
lean_dec(v_x_406_);
v_res_411_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_404_, v_x_3522__boxed_409_, v_x_3523__boxed_410_, v_x_407_, v_x_408_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
uint64_t v___x_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; 
v___x_415_ = l_Lean_instHashableMVarId_hash(v_x_413_);
v___x_416_ = lean_uint64_to_usize(v___x_415_);
v___x_417_ = ((size_t)1ULL);
v___x_418_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_412_, v___x_416_, v___x_417_, v_x_413_, v_x_414_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(lean_object* v_mvarId_419_, lean_object* v_val_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; lean_object* v_mctx_424_; lean_object* v_cache_425_; lean_object* v_zetaDeltaFVarIds_426_; lean_object* v_postponed_427_; lean_object* v_diag_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_455_; 
v___x_423_ = lean_st_ref_take(v___y_421_);
v_mctx_424_ = lean_ctor_get(v___x_423_, 0);
v_cache_425_ = lean_ctor_get(v___x_423_, 1);
v_zetaDeltaFVarIds_426_ = lean_ctor_get(v___x_423_, 2);
v_postponed_427_ = lean_ctor_get(v___x_423_, 3);
v_diag_428_ = lean_ctor_get(v___x_423_, 4);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_455_ == 0)
{
v___x_430_ = v___x_423_;
v_isShared_431_ = v_isSharedCheck_455_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_diag_428_);
lean_inc(v_postponed_427_);
lean_inc(v_zetaDeltaFVarIds_426_);
lean_inc(v_cache_425_);
lean_inc(v_mctx_424_);
lean_dec(v___x_423_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_455_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_depth_432_; lean_object* v_levelAssignDepth_433_; lean_object* v_mvarCounter_434_; lean_object* v_lDepth_435_; lean_object* v_decls_436_; lean_object* v_userNames_437_; lean_object* v_lAssignment_438_; lean_object* v_eAssignment_439_; lean_object* v_dAssignment_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_454_; 
v_depth_432_ = lean_ctor_get(v_mctx_424_, 0);
v_levelAssignDepth_433_ = lean_ctor_get(v_mctx_424_, 1);
v_mvarCounter_434_ = lean_ctor_get(v_mctx_424_, 2);
v_lDepth_435_ = lean_ctor_get(v_mctx_424_, 3);
v_decls_436_ = lean_ctor_get(v_mctx_424_, 4);
v_userNames_437_ = lean_ctor_get(v_mctx_424_, 5);
v_lAssignment_438_ = lean_ctor_get(v_mctx_424_, 6);
v_eAssignment_439_ = lean_ctor_get(v_mctx_424_, 7);
v_dAssignment_440_ = lean_ctor_get(v_mctx_424_, 8);
v_isSharedCheck_454_ = !lean_is_exclusive(v_mctx_424_);
if (v_isSharedCheck_454_ == 0)
{
v___x_442_ = v_mctx_424_;
v_isShared_443_ = v_isSharedCheck_454_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_dAssignment_440_);
lean_inc(v_eAssignment_439_);
lean_inc(v_lAssignment_438_);
lean_inc(v_userNames_437_);
lean_inc(v_decls_436_);
lean_inc(v_lDepth_435_);
lean_inc(v_mvarCounter_434_);
lean_inc(v_levelAssignDepth_433_);
lean_inc(v_depth_432_);
lean_dec(v_mctx_424_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_454_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(v_eAssignment_439_, v_mvarId_419_, v_val_420_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 7, v___x_444_);
v___x_446_ = v___x_442_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_depth_432_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_levelAssignDepth_433_);
lean_ctor_set(v_reuseFailAlloc_453_, 2, v_mvarCounter_434_);
lean_ctor_set(v_reuseFailAlloc_453_, 3, v_lDepth_435_);
lean_ctor_set(v_reuseFailAlloc_453_, 4, v_decls_436_);
lean_ctor_set(v_reuseFailAlloc_453_, 5, v_userNames_437_);
lean_ctor_set(v_reuseFailAlloc_453_, 6, v_lAssignment_438_);
lean_ctor_set(v_reuseFailAlloc_453_, 7, v___x_444_);
lean_ctor_set(v_reuseFailAlloc_453_, 8, v_dAssignment_440_);
v___x_446_ = v_reuseFailAlloc_453_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_448_; 
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_446_);
v___x_448_ = v___x_430_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_cache_425_);
lean_ctor_set(v_reuseFailAlloc_452_, 2, v_zetaDeltaFVarIds_426_);
lean_ctor_set(v_reuseFailAlloc_452_, 3, v_postponed_427_);
lean_ctor_set(v_reuseFailAlloc_452_, 4, v_diag_428_);
v___x_448_ = v_reuseFailAlloc_452_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_st_ref_set(v___y_421_, v___x_448_);
v___x_450_ = lean_box(0);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
return v___x_451_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg___boxed(lean_object* v_mvarId_456_, lean_object* v_val_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(v_mvarId_456_, v_val_457_, v___y_458_);
lean_dec(v___y_458_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(lean_object* v_msgData_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; lean_object* v_env_468_; lean_object* v___x_469_; lean_object* v_mctx_470_; lean_object* v_lctx_471_; lean_object* v_options_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_467_ = lean_st_ref_get(v___y_465_);
v_env_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_env_468_);
lean_dec(v___x_467_);
v___x_469_ = lean_st_ref_get(v___y_463_);
v_mctx_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc_ref(v_mctx_470_);
lean_dec(v___x_469_);
v_lctx_471_ = lean_ctor_get(v___y_462_, 2);
v_options_472_ = lean_ctor_get(v___y_464_, 2);
lean_inc_ref(v_options_472_);
lean_inc_ref(v_lctx_471_);
v___x_473_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_473_, 0, v_env_468_);
lean_ctor_set(v___x_473_, 1, v_mctx_470_);
lean_ctor_set(v___x_473_, 2, v_lctx_471_);
lean_ctor_set(v___x_473_, 3, v_options_472_);
v___x_474_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v_msgData_461_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2___boxed(lean_object* v_msgData_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msgData_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(lean_object* v_msg_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_ref_489_; lean_object* v___x_490_; lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_499_; 
v_ref_489_ = lean_ctor_get(v___y_486_, 5);
v___x_490_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msg_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_499_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
lean_inc(v_ref_489_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v_ref_489_);
lean_ctor_set(v___x_495_, 1, v_a_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 1);
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg___boxed(lean_object* v_msg_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(v_msg_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
return v_res_506_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0));
v___x_509_ = l_Lean_stringToMessageData(v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2));
v___x_512_ = l_Lean_stringToMessageData(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4));
v___x_515_ = l_Lean_stringToMessageData(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0(lean_object* v_mvar_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
lean_inc(v_mvar_516_);
v___x_522_ = l_Lean_MVarId_getType(v_mvar_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; lean_object* v_a_525_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___x_600_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref(v___x_522_);
v___x_524_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(v_a_523_, v___y_518_);
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref(v___x_524_);
lean_inc(v_a_525_);
v___x_600_ = l_Lean_Meta_isProp(v_a_525_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; uint8_t v___x_602_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref(v___x_600_);
v___x_602_ = lean_unbox(v_a_601_);
lean_dec(v_a_601_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; 
lean_inc(v___y_520_);
lean_inc_ref(v___y_519_);
lean_inc(v___y_518_);
lean_inc_ref(v___y_517_);
v___x_603_ = lean_infer_type(v_a_525_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_object* v_a_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v_a_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
v_a_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_a_604_);
lean_dec_ref(v___x_603_);
v___x_605_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1);
v___x_606_ = l_Lean_mkMVar(v_mvar_516_);
v___x_607_ = l_Lean_MessageData_ofExpr(v___x_606_);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l_Lean_MessageData_ofExpr(v_a_604_);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(v___x_614_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
v_a_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_a_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_616_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v_mvar_516_);
v_a_624_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_603_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_603_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
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
else
{
v___y_527_ = v___y_517_;
v___y_528_ = v___y_518_;
v___y_529_ = v___y_519_;
v___y_530_ = v___y_520_;
goto v___jp_526_;
}
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v_a_525_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v_mvar_516_);
v_a_632_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_600_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_600_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
v___jp_526_:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Elab_Tactic_Do_ProofMode_mStart(v_a_525_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_591_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_591_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_591_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_591_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v_proof_x3f_536_; 
v_proof_x3f_536_ = lean_ctor_get(v_a_532_, 1);
if (lean_obj_tag(v_proof_x3f_536_) == 1)
{
lean_object* v_goal_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_577_; 
lean_inc_ref(v_proof_x3f_536_);
lean_del_object(v___x_534_);
v_goal_537_ = lean_ctor_get(v_a_532_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v_a_532_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v_a_532_, 1);
lean_dec(v_unused_578_);
v___x_539_ = v_a_532_;
v_isShared_540_ = v_isSharedCheck_577_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_goal_537_);
lean_dec(v_a_532_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_577_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v_val_541_; lean_object* v___x_542_; 
v_val_541_ = lean_ctor_get(v_proof_x3f_536_, 0);
lean_inc(v_val_541_);
lean_dec_ref(v_proof_x3f_536_);
lean_inc(v_mvar_516_);
v___x_542_ = l_Lean_MVarId_getTag(v_mvar_516_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref(v___x_542_);
lean_inc_ref(v_goal_537_);
v___x_544_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_537_);
v___x_545_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_544_, v_a_543_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec_ref(v___y_527_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_559_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref(v___x_545_);
lean_inc(v_a_546_);
v___x_547_ = l_Lean_Expr_app___override(v_val_541_, v_a_546_);
v___x_548_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(v_mvar_516_, v___x_547_, v___y_528_);
lean_dec(v___y_528_);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; 
v_unused_560_ = lean_ctor_get(v___x_548_, 0);
lean_dec(v_unused_560_);
v___x_550_ = v___x_548_;
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
else
{
lean_dec(v___x_548_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = l_Lean_Expr_mvarId_x21(v_a_546_);
lean_dec(v_a_546_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v_goal_537_);
lean_ctor_set(v___x_539_, 0, v___x_552_);
v___x_554_ = v___x_539_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_goal_537_);
v___x_554_ = v_reuseFailAlloc_558_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_554_);
v___x_556_ = v___x_550_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
lean_dec(v_val_541_);
lean_del_object(v___x_539_);
lean_dec_ref(v_goal_537_);
lean_dec(v___y_528_);
lean_dec(v_mvar_516_);
v_a_561_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_545_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_545_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v_val_541_);
lean_del_object(v___x_539_);
lean_dec_ref(v_goal_537_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v_mvar_516_);
v_a_569_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_542_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_542_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
else
{
lean_object* v_goal_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_589_; 
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
v_goal_579_ = lean_ctor_get(v_a_532_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v_a_532_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v_a_532_, 1);
lean_dec(v_unused_590_);
v___x_581_ = v_a_532_;
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_goal_579_);
lean_dec(v_a_532_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_589_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_goal_579_);
lean_ctor_set(v___x_581_, 0, v_mvar_516_);
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_mvar_516_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_goal_579_);
v___x_584_ = v_reuseFailAlloc_588_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_586_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_584_);
v___x_586_ = v___x_534_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v___x_584_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v_mvar_516_);
v_a_592_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_531_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_531_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v_mvar_516_);
v_a_640_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_522_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_522_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___boxed(lean_object* v_mvar_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0(v_mvar_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(lean_object* v_mvar_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v___f_661_; lean_object* v___x_662_; 
lean_inc(v_mvar_655_);
v___f_661_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___boxed), 6, 1);
lean_closure_set(v___f_661_, 0, v_mvar_655_);
v___x_662_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(v_mvar_655_, v___f_661_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___boxed(lean_object* v_mvar_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(v_mvar_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0(lean_object* v_mvarId_670_, lean_object* v_val_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(v_mvarId_670_, v_val_671_, v___y_673_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___boxed(lean_object* v_mvarId_678_, lean_object* v_val_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0(v_mvarId_678_, v_val_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1(lean_object* v_00_u03b1_686_, lean_object* v_msg_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(v_msg_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___boxed(lean_object* v_00_u03b1_694_, lean_object* v_msg_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1(v_00_u03b1_694_, v_msg_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0(lean_object* v_00_u03b2_702_, lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(v_x_703_, v_x_704_, v_x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_707_, lean_object* v_x_708_, size_t v_x_709_, size_t v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_708_, v_x_709_, v_x_710_, v_x_711_, v_x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
size_t v_x_4144__boxed_720_; size_t v_x_4145__boxed_721_; lean_object* v_res_722_; 
v_x_4144__boxed_720_ = lean_unbox_usize(v_x_716_);
lean_dec(v_x_716_);
v_x_4145__boxed_721_ = lean_unbox_usize(v_x_717_);
lean_dec(v_x_717_);
v_res_722_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2(v_00_u03b2_714_, v_x_715_, v_x_4144__boxed_720_, v_x_4145__boxed_721_, v_x_718_, v_x_719_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_723_, lean_object* v_n_724_, lean_object* v_k_725_, lean_object* v_v_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5___redArg(v_n_724_, v_k_725_, v_v_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_728_, size_t v_depth_729_, lean_object* v_keys_730_, lean_object* v_vals_731_, lean_object* v_heq_732_, lean_object* v_i_733_, lean_object* v_entries_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_729_, v_keys_730_, v_vals_731_, v_i_733_, v_entries_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_736_, lean_object* v_depth_737_, lean_object* v_keys_738_, lean_object* v_vals_739_, lean_object* v_heq_740_, lean_object* v_i_741_, lean_object* v_entries_742_){
_start:
{
size_t v_depth_boxed_743_; lean_object* v_res_744_; 
v_depth_boxed_743_ = lean_unbox_usize(v_depth_737_);
lean_dec(v_depth_737_);
v_res_744_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_736_, v_depth_boxed_743_, v_keys_738_, v_vals_739_, v_heq_740_, v_i_741_, v_entries_742_);
lean_dec_ref(v_vals_739_);
lean_dec_ref(v_keys_738_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_746_, v_x_747_, v_x_748_, v_x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_object* v_a_758_; lean_object* v___x_759_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
lean_inc(v_a_758_);
lean_dec_ref(v___x_757_);
v___x_759_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(v_a_758_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v_fst_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref(v___x_759_);
v_fst_761_ = lean_ctor_get(v_a_760_, 0);
v___x_762_ = lean_box(0);
lean_inc(v_fst_761_);
v___x_763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_763_, 0, v_fst_761_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_763_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_771_ == 0)
{
lean_object* v_unused_772_; 
v_unused_772_ = lean_ctor_get(v___x_764_, 0);
lean_dec(v_unused_772_);
v___x_766_ = v___x_764_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_dec(v___x_764_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 0, v_a_760_);
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_760_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_a_760_);
v_a_773_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_764_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_764_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
return v___x_759_;
}
}
else
{
lean_object* v_a_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_788_; 
v_a_781_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_788_ == 0)
{
v___x_783_ = v___x_757_;
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_a_781_);
lean_dec(v___x_757_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_788_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_a_781_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg___boxed(lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal(lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_797_, v_a_800_, v_a_801_, v_a_802_, v_a_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___boxed(lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal(v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec(v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_830_; 
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v___x_822_, 0);
lean_dec(v_unused_831_);
v___x_824_ = v___x_822_;
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
else
{
lean_dec(v___x_822_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_830_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = lean_box(0);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 0, v___x_826_);
v___x_828_ = v___x_824_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_a_832_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_822_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_822_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg___boxed(lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
lean_dec(v_a_840_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart(lean_object* v_x_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(v_a_849_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___boxed(lean_object* v_x_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart(v_x_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
lean_dec(v_a_862_);
lean_dec_ref(v_a_861_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
lean_dec(v_x_858_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1(){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_887_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_888_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3));
v___x_889_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6));
v___x_890_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___boxed), 10, 0);
v___x_891_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_887_, v___x_888_, v___x_889_, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___boxed(lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1();
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(lean_object* v_e_894_, lean_object* v___y_895_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = l_Lean_Expr_hasMVar(v_e_894_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v_e_894_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v_mctx_900_; lean_object* v___x_901_; lean_object* v_fst_902_; lean_object* v_snd_903_; lean_object* v___x_904_; lean_object* v_cache_905_; lean_object* v_zetaDeltaFVarIds_906_; lean_object* v_postponed_907_; lean_object* v_diag_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_917_; 
v___x_899_ = lean_st_ref_get(v___y_895_);
v_mctx_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc_ref(v_mctx_900_);
lean_dec(v___x_899_);
v___x_901_ = l_Lean_instantiateMVarsCore(v_mctx_900_, v_e_894_);
v_fst_902_ = lean_ctor_get(v___x_901_, 0);
lean_inc(v_fst_902_);
v_snd_903_ = lean_ctor_get(v___x_901_, 1);
lean_inc(v_snd_903_);
lean_dec_ref(v___x_901_);
v___x_904_ = lean_st_ref_take(v___y_895_);
v_cache_905_ = lean_ctor_get(v___x_904_, 1);
v_zetaDeltaFVarIds_906_ = lean_ctor_get(v___x_904_, 2);
v_postponed_907_ = lean_ctor_get(v___x_904_, 3);
v_diag_908_ = lean_ctor_get(v___x_904_, 4);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_917_ == 0)
{
lean_object* v_unused_918_; 
v_unused_918_ = lean_ctor_get(v___x_904_, 0);
lean_dec(v_unused_918_);
v___x_910_ = v___x_904_;
v_isShared_911_ = v_isSharedCheck_917_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_diag_908_);
lean_inc(v_postponed_907_);
lean_inc(v_zetaDeltaFVarIds_906_);
lean_inc(v_cache_905_);
lean_dec(v___x_904_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_917_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v_snd_903_);
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_snd_903_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_cache_905_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_zetaDeltaFVarIds_906_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_postponed_907_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_diag_908_);
v___x_913_ = v_reuseFailAlloc_916_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_st_ref_set(v___y_895_, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v_fst_902_);
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg___boxed(lean_object* v_e_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(v_e_919_, v___y_920_);
lean_dec(v___y_920_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0(lean_object* v_e_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(v_e_923_, v___y_929_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___boxed(lean_object* v_e_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0(v_e_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0(lean_object* v_x_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_955_; 
lean_inc(v___y_949_);
lean_inc_ref(v___y_948_);
lean_inc(v___y_947_);
lean_inc_ref(v___y_946_);
v___x_955_ = lean_apply_9(v_x_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, lean_box(0));
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0___boxed(lean_object* v_x_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0(v_x_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_960_);
lean_dec_ref(v___y_959_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(lean_object* v_mvarId_967_, lean_object* v_x_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___f_978_; lean_object* v___x_979_; 
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
v___f_978_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_978_, 0, v_x_968_);
lean_closure_set(v___f_978_, 1, v___y_969_);
lean_closure_set(v___f_978_, 2, v___y_970_);
lean_closure_set(v___f_978_, 3, v___y_971_);
lean_closure_set(v___f_978_, 4, v___y_972_);
v___x_979_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_967_, v___f_978_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
if (lean_obj_tag(v___x_979_) == 0)
{
return v___x_979_;
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_979_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_979_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___boxed(lean_object* v_mvarId_988_, lean_object* v_x_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(v_mvarId_988_, v_x_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2(lean_object* v_00_u03b1_1000_, lean_object* v_mvarId_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(v_mvarId_1001_, v_x_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___boxed(lean_object* v_00_u03b1_1013_, lean_object* v_mvarId_1014_, lean_object* v_x_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2(v_00_u03b1_1013_, v_mvarId_1014_, v_x_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(lean_object* v_msg_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_ref_1032_; lean_object* v___x_1033_; lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1042_; 
v_ref_1032_ = lean_ctor_get(v___y_1029_, 5);
v___x_1033_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msg_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1042_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1040_; 
lean_inc(v_ref_1032_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v_ref_1032_);
lean_ctor_set(v___x_1038_, 1, v_a_1034_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 1);
lean_ctor_set(v___x_1036_, 0, v___x_1038_);
v___x_1040_ = v___x_1036_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg___boxed(lean_object* v_msg_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(v_msg_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1049_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0));
v___x_1052_ = l_Lean_stringToMessageData(v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0(lean_object* v_a_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
lean_inc(v_a_1053_);
v___x_1063_ = l_Lean_MVarId_getType(v_a_1053_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1065_; lean_object* v_a_1066_; lean_object* v___x_1067_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
lean_inc(v_a_1064_);
lean_dec_ref(v___x_1063_);
v___x_1065_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(v_a_1064_, v___y_1059_);
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref(v___x_1065_);
v___x_1067_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1066_);
lean_dec(v_a_1066_);
if (lean_obj_tag(v___x_1067_) == 1)
{
lean_object* v_val_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_val_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_val_1068_);
lean_dec_ref(v___x_1067_);
v___x_1069_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(v_val_1068_);
v___x_1070_ = l_Lean_MVarId_setType___redArg(v_a_1053_, v___x_1069_, v___y_1059_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
lean_dec(v___x_1067_);
lean_dec(v_a_1053_);
v___x_1071_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1);
v___x_1072_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(v___x_1071_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1072_;
}
}
else
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1080_; 
lean_dec(v_a_1053_);
v_a_1073_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1080_ == 0)
{
v___x_1075_ = v___x_1063_;
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1063_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1080_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1078_; 
if (v_isShared_1076_ == 0)
{
v___x_1078_ = v___x_1075_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_a_1073_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___boxed(lean_object* v_a_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0(v_a_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1093_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___f_1103_; lean_object* v___x_1104_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref(v___x_1101_);
lean_inc(v_a_1102_);
v___f_1103_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1103_, 0, v_a_1102_);
v___x_1104_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(v_a_1102_, v___f_1103_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
return v___x_1104_;
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
v_a_1105_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1101_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1101_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___boxed(lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
lean_dec(v_a_1120_);
lean_dec_ref(v_a_1119_);
lean_dec(v_a_1118_);
lean_dec_ref(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop(lean_object* v_x_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___boxed(lean_object* v_x_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop(v_x_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_x_1134_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1(lean_object* v_00_u03b1_1145_, lean_object* v_msg_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(v_msg_1146_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___boxed(lean_object* v_00_u03b1_1157_, lean_object* v_msg_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1(v_00_u03b1_1157_, v_msg_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1165_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1(){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1184_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1185_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1));
v___x_1186_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3));
v___x_1187_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___boxed), 10, 0);
v___x_1188_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1184_, v___x_1185_, v___x_1186_, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___boxed(lean_object* v_a_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1();
return v_res_1190_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
