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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(lean_object*);
lean_object* l_Lean_MVarId_setType___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0;
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mstart"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(12, 72, 234, 250, 239, 149, 139, 165)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMStart"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(74, 124, 237, 138, 104, 184, 13, 121)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mstop"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 209, 80, 25, 253, 26, 68, 170)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabMStop"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__7_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 207, 43, 105, 62, 50, 202, 255)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___boxed(lean_object*);
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
v___x_19_ = lean_st_ref_put(v___y_2_, v___x_18_);
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
v___x_62_ = lean_st_ref_put(v___y_43_, v___x_61_);
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
lean_inc_n(v_a_127_, 2);
lean_dec_ref_known(v___x_126_, 1);
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
lean_inc_n(v_a_133_, 2);
lean_dec_ref_known(v___x_132_, 1);
v___x_134_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__3));
v___x_135_ = lean_box(0);
lean_inc(v_a_127_);
v___x_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_136_, 0, v_a_127_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
lean_inc_ref(v___x_136_);
v___x_137_ = l_Lean_mkConst(v___x_134_, v___x_136_);
v___x_138_ = l_Lean_Expr_app___override(v___x_137_, v_a_133_);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
v___x_140_ = l_Lean_Meta_mkFreshExprMVar(v___x_139_, v___x_130_, v___x_131_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc_n(v_a_141_, 2);
lean_dec_ref_known(v___x_140_, 1);
v___x_142_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mStart___closed__6));
v___x_143_ = l_Lean_mkConst(v___x_142_, v___x_136_);
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
lean_dec_ref_known(v___x_146_, 1);
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
lean_dec_ref_known(v___x_136_, 2);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(lean_object* v_x_298_, size_t v_x_299_, size_t v_x_300_, lean_object* v_x_301_, lean_object* v_x_302_){
_start:
{
if (lean_obj_tag(v_x_298_) == 0)
{
lean_object* v_es_303_; size_t v___x_304_; size_t v___x_305_; lean_object* v_j_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v_es_303_ = lean_ctor_get(v_x_298_, 0);
v___x_304_ = ((size_t)31ULL);
v___x_305_ = lean_usize_land(v_x_299_, v___x_304_);
v_j_306_ = lean_usize_to_nat(v___x_305_);
v___x_307_ = lean_array_get_size(v_es_303_);
v___x_308_ = lean_nat_dec_lt(v_j_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_dec(v_j_306_);
lean_dec(v_x_302_);
lean_dec(v_x_301_);
return v_x_298_;
}
else
{
lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_347_; 
lean_inc_ref(v_es_303_);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_298_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_x_298_, 0);
lean_dec(v_unused_348_);
v___x_310_ = v_x_298_;
v_isShared_311_ = v_isSharedCheck_347_;
goto v_resetjp_309_;
}
else
{
lean_dec(v_x_298_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_347_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v_v_312_; lean_object* v___x_313_; lean_object* v_xs_x27_314_; lean_object* v___y_316_; 
v_v_312_ = lean_array_fget(v_es_303_, v_j_306_);
v___x_313_ = lean_box(0);
v_xs_x27_314_ = lean_array_fset(v_es_303_, v_j_306_, v___x_313_);
switch(lean_obj_tag(v_v_312_))
{
case 0:
{
lean_object* v_key_321_; lean_object* v_val_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_332_; 
v_key_321_ = lean_ctor_get(v_v_312_, 0);
v_val_322_ = lean_ctor_get(v_v_312_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_v_312_);
if (v_isSharedCheck_332_ == 0)
{
v___x_324_ = v_v_312_;
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_val_322_);
lean_inc(v_key_321_);
lean_dec(v_v_312_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
uint8_t v___x_326_; 
v___x_326_ = l_Lean_instBEqMVarId_beq(v_x_301_, v_key_321_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_del_object(v___x_324_);
v___x_327_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_321_, v_val_322_, v_x_301_, v_x_302_);
v___x_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
v___y_316_ = v___x_328_;
goto v___jp_315_;
}
else
{
lean_object* v___x_330_; 
lean_dec(v_val_322_);
lean_dec(v_key_321_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v_x_302_);
lean_ctor_set(v___x_324_, 0, v_x_301_);
v___x_330_ = v___x_324_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_x_301_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_x_302_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
v___y_316_ = v___x_330_;
goto v___jp_315_;
}
}
}
}
case 1:
{
lean_object* v_node_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_345_; 
v_node_333_ = lean_ctor_get(v_v_312_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v_v_312_);
if (v_isSharedCheck_345_ == 0)
{
v___x_335_ = v_v_312_;
v_isShared_336_ = v_isSharedCheck_345_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_node_333_);
lean_dec(v_v_312_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_345_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; lean_object* v___x_341_; lean_object* v___x_343_; 
v___x_337_ = ((size_t)5ULL);
v___x_338_ = lean_usize_shift_right(v_x_299_, v___x_337_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_add(v_x_300_, v___x_339_);
v___x_341_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_node_333_, v___x_338_, v___x_340_, v_x_301_, v_x_302_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_341_);
v___x_343_ = v___x_335_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
v___y_316_ = v___x_343_;
goto v___jp_315_;
}
}
}
default: 
{
lean_object* v___x_346_; 
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v_x_301_);
lean_ctor_set(v___x_346_, 1, v_x_302_);
v___y_316_ = v___x_346_;
goto v___jp_315_;
}
}
v___jp_315_:
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_array_fset(v_xs_x27_314_, v_j_306_, v___y_316_);
lean_dec(v_j_306_);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_317_);
v___x_319_ = v___x_310_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
else
{
lean_object* v_ks_349_; lean_object* v_vs_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_368_; 
v_ks_349_ = lean_ctor_get(v_x_298_, 0);
v_vs_350_ = lean_ctor_get(v_x_298_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v_x_298_);
if (v_isSharedCheck_368_ == 0)
{
v___x_352_ = v_x_298_;
v_isShared_353_ = v_isSharedCheck_368_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_vs_350_);
lean_inc(v_ks_349_);
lean_dec(v_x_298_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_368_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_ks_349_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_vs_350_);
v___x_355_ = v_reuseFailAlloc_367_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v_newNode_356_; size_t v___x_357_; uint8_t v___x_358_; 
v_newNode_356_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5___redArg(v___x_355_, v_x_301_, v_x_302_);
v___x_357_ = ((size_t)7ULL);
v___x_358_ = lean_usize_dec_le(v___x_357_, v_x_300_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_359_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_356_);
v___x_360_ = lean_unsigned_to_nat(4u);
v___x_361_ = lean_nat_dec_lt(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
if (v___x_361_ == 0)
{
lean_object* v_ks_362_; lean_object* v_vs_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_ks_362_ = lean_ctor_get(v_newNode_356_, 0);
lean_inc_ref(v_ks_362_);
v_vs_363_ = lean_ctor_get(v_newNode_356_, 1);
lean_inc_ref(v_vs_363_);
lean_dec_ref(v_newNode_356_);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_366_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_x_300_, v_ks_362_, v_vs_363_, v___x_364_, v___x_365_);
lean_dec_ref(v_vs_363_);
lean_dec_ref(v_ks_362_);
return v___x_366_;
}
else
{
return v_newNode_356_;
}
}
else
{
return v_newNode_356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(size_t v_depth_369_, lean_object* v_keys_370_, lean_object* v_vals_371_, lean_object* v_i_372_, lean_object* v_entries_373_){
_start:
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = lean_array_get_size(v_keys_370_);
v___x_375_ = lean_nat_dec_lt(v_i_372_, v___x_374_);
if (v___x_375_ == 0)
{
lean_dec(v_i_372_);
return v_entries_373_;
}
else
{
lean_object* v_k_376_; lean_object* v_v_377_; uint64_t v___x_378_; size_t v_h_379_; size_t v___x_380_; lean_object* v___x_381_; size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; size_t v_h_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v_k_376_ = lean_array_fget_borrowed(v_keys_370_, v_i_372_);
v_v_377_ = lean_array_fget_borrowed(v_vals_371_, v_i_372_);
v___x_378_ = l_Lean_instHashableMVarId_hash(v_k_376_);
v_h_379_ = lean_uint64_to_usize(v___x_378_);
v___x_380_ = ((size_t)5ULL);
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_sub(v_depth_369_, v___x_382_);
v___x_384_ = lean_usize_mul(v___x_380_, v___x_383_);
v_h_385_ = lean_usize_shift_right(v_h_379_, v___x_384_);
v___x_386_ = lean_nat_add(v_i_372_, v___x_381_);
lean_dec(v_i_372_);
lean_inc(v_v_377_);
lean_inc(v_k_376_);
v___x_387_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_entries_373_, v_h_385_, v_depth_369_, v_k_376_, v_v_377_);
v_i_372_ = v___x_386_;
v_entries_373_ = v___x_387_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_depth_389_, lean_object* v_keys_390_, lean_object* v_vals_391_, lean_object* v_i_392_, lean_object* v_entries_393_){
_start:
{
size_t v_depth_boxed_394_; lean_object* v_res_395_; 
v_depth_boxed_394_ = lean_unbox_usize(v_depth_389_);
lean_dec(v_depth_389_);
v_res_395_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_boxed_394_, v_keys_390_, v_vals_391_, v_i_392_, v_entries_393_);
lean_dec_ref(v_vals_391_);
lean_dec_ref(v_keys_390_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
size_t v_x_3308__boxed_401_; size_t v_x_3309__boxed_402_; lean_object* v_res_403_; 
v_x_3308__boxed_401_ = lean_unbox_usize(v_x_397_);
lean_dec(v_x_397_);
v_x_3309__boxed_402_ = lean_unbox_usize(v_x_398_);
lean_dec(v_x_398_);
v_res_403_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_396_, v_x_3308__boxed_401_, v_x_3309__boxed_402_, v_x_399_, v_x_400_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(lean_object* v_x_404_, lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
uint64_t v___x_407_; size_t v___x_408_; size_t v___x_409_; lean_object* v___x_410_; 
v___x_407_ = l_Lean_instHashableMVarId_hash(v_x_405_);
v___x_408_ = lean_uint64_to_usize(v___x_407_);
v___x_409_ = ((size_t)1ULL);
v___x_410_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_404_, v___x_408_, v___x_409_, v_x_405_, v_x_406_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(lean_object* v_mvarId_411_, lean_object* v_val_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; lean_object* v_mctx_416_; lean_object* v_cache_417_; lean_object* v_zetaDeltaFVarIds_418_; lean_object* v_postponed_419_; lean_object* v_diag_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_449_; 
v___x_415_ = lean_st_ref_take(v___y_413_);
v_mctx_416_ = lean_ctor_get(v___x_415_, 0);
v_cache_417_ = lean_ctor_get(v___x_415_, 1);
v_zetaDeltaFVarIds_418_ = lean_ctor_get(v___x_415_, 2);
v_postponed_419_ = lean_ctor_get(v___x_415_, 3);
v_diag_420_ = lean_ctor_get(v___x_415_, 4);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_415_);
if (v_isSharedCheck_449_ == 0)
{
v___x_422_ = v___x_415_;
v_isShared_423_ = v_isSharedCheck_449_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_diag_420_);
lean_inc(v_postponed_419_);
lean_inc(v_zetaDeltaFVarIds_418_);
lean_inc(v_cache_417_);
lean_inc(v_mctx_416_);
lean_dec(v___x_415_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_449_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_depth_424_; lean_object* v_levelAssignDepth_425_; lean_object* v_lmvarCounter_426_; lean_object* v_mvarCounter_427_; lean_object* v_lDecls_428_; lean_object* v_decls_429_; lean_object* v_userNames_430_; lean_object* v_lAssignment_431_; lean_object* v_eAssignment_432_; lean_object* v_dAssignment_433_; lean_object* v_instanceTypedMVars_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_448_; 
v_depth_424_ = lean_ctor_get(v_mctx_416_, 0);
v_levelAssignDepth_425_ = lean_ctor_get(v_mctx_416_, 1);
v_lmvarCounter_426_ = lean_ctor_get(v_mctx_416_, 2);
v_mvarCounter_427_ = lean_ctor_get(v_mctx_416_, 3);
v_lDecls_428_ = lean_ctor_get(v_mctx_416_, 4);
v_decls_429_ = lean_ctor_get(v_mctx_416_, 5);
v_userNames_430_ = lean_ctor_get(v_mctx_416_, 6);
v_lAssignment_431_ = lean_ctor_get(v_mctx_416_, 7);
v_eAssignment_432_ = lean_ctor_get(v_mctx_416_, 8);
v_dAssignment_433_ = lean_ctor_get(v_mctx_416_, 9);
v_instanceTypedMVars_434_ = lean_ctor_get(v_mctx_416_, 10);
v_isSharedCheck_448_ = !lean_is_exclusive(v_mctx_416_);
if (v_isSharedCheck_448_ == 0)
{
v___x_436_ = v_mctx_416_;
v_isShared_437_ = v_isSharedCheck_448_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_instanceTypedMVars_434_);
lean_inc(v_dAssignment_433_);
lean_inc(v_eAssignment_432_);
lean_inc(v_lAssignment_431_);
lean_inc(v_userNames_430_);
lean_inc(v_decls_429_);
lean_inc(v_lDecls_428_);
lean_inc(v_mvarCounter_427_);
lean_inc(v_lmvarCounter_426_);
lean_inc(v_levelAssignDepth_425_);
lean_inc(v_depth_424_);
lean_dec(v_mctx_416_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_448_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_438_ = lean_box(0);
v___x_439_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(v_eAssignment_432_, v_mvarId_411_, v_val_412_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 8, v___x_439_);
v___x_441_ = v___x_436_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_depth_424_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_levelAssignDepth_425_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_lmvarCounter_426_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_mvarCounter_427_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_lDecls_428_);
lean_ctor_set(v_reuseFailAlloc_447_, 5, v_decls_429_);
lean_ctor_set(v_reuseFailAlloc_447_, 6, v_userNames_430_);
lean_ctor_set(v_reuseFailAlloc_447_, 7, v_lAssignment_431_);
lean_ctor_set(v_reuseFailAlloc_447_, 8, v___x_439_);
lean_ctor_set(v_reuseFailAlloc_447_, 9, v_dAssignment_433_);
lean_ctor_set(v_reuseFailAlloc_447_, 10, v_instanceTypedMVars_434_);
v___x_441_ = v_reuseFailAlloc_447_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_443_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_441_);
v___x_443_ = v___x_422_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_cache_417_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_zetaDeltaFVarIds_418_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_postponed_419_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v_diag_420_);
v___x_443_ = v_reuseFailAlloc_446_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_st_ref_put(v___y_413_, v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v___x_438_);
return v___x_445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg___boxed(lean_object* v_mvarId_450_, lean_object* v_val_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(v_mvarId_450_, v_val_451_, v___y_452_);
lean_dec(v___y_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(lean_object* v_msgData_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; lean_object* v_env_462_; uint8_t v___x_463_; lean_object* v_env_464_; lean_object* v___x_465_; lean_object* v_toCold_466_; lean_object* v_mctx_467_; lean_object* v_lctx_468_; lean_object* v_options_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_461_ = lean_st_ref_get(v___y_459_);
v_env_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc_ref(v_env_462_);
lean_dec(v___x_461_);
v___x_463_ = 0;
v_env_464_ = l_Lean_Environment_setRecordingDeps(v_env_462_, v___x_463_);
v___x_465_ = lean_st_ref_get(v___y_457_);
v_toCold_466_ = lean_ctor_get(v___y_458_, 0);
v_mctx_467_ = lean_ctor_get(v___x_465_, 0);
lean_inc_ref(v_mctx_467_);
lean_dec(v___x_465_);
v_lctx_468_ = lean_ctor_get(v___y_456_, 2);
v_options_469_ = lean_ctor_get(v_toCold_466_, 2);
lean_inc_ref(v_options_469_);
lean_inc_ref(v_lctx_468_);
v___x_470_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_470_, 0, v_env_464_);
lean_ctor_set(v___x_470_, 1, v_mctx_467_);
lean_ctor_set(v___x_470_, 2, v_lctx_468_);
lean_ctor_set(v___x_470_, 3, v_options_469_);
v___x_471_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v_msgData_455_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2___boxed(lean_object* v_msgData_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msgData_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_ref_486_; lean_object* v___x_487_; lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_496_; 
v_ref_486_ = lean_ctor_get(v___y_483_, 2);
v___x_487_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_496_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_496_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_494_; 
lean_inc(v_ref_486_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v_ref_486_);
lean_ctor_set(v___x_492_, 1, v_a_488_);
if (v_isShared_491_ == 0)
{
lean_ctor_set_tag(v___x_490_, 1);
lean_ctor_set(v___x_490_, 0, v___x_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg___boxed(lean_object* v_msg_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(v_msg_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_503_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__0));
v___x_506_ = l_Lean_stringToMessageData(v___x_505_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__2));
v___x_509_ = l_Lean_stringToMessageData(v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__4));
v___x_512_ = l_Lean_stringToMessageData(v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0(lean_object* v_mvar_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v___x_519_; 
lean_inc(v_mvar_513_);
v___x_519_ = l_Lean_MVarId_getType(v_mvar_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_521_; lean_object* v_a_522_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___x_597_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mStart_spec__1___redArg(v_a_520_, v___y_515_);
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_n(v_a_522_, 2);
lean_dec_ref(v___x_521_);
v___x_597_ = l_Lean_Meta_isProp(v_a_522_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; uint8_t v___x_599_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = lean_unbox(v_a_598_);
lean_dec(v_a_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
lean_inc(v___y_515_);
lean_inc_ref(v___y_514_);
v___x_600_ = lean_infer_type(v_a_522_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_600_) == 0)
{
lean_object* v_a_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
v_a_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_a_601_);
lean_dec_ref_known(v___x_600_, 1);
v___x_602_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__1);
v___x_603_ = l_Lean_mkMVar(v_mvar_513_);
v___x_604_ = l_Lean_MessageData_ofExpr(v___x_603_);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_602_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__3);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Lean_MessageData_ofExpr(v_a_601_);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_607_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___closed__5);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(v___x_611_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_628_; 
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v_mvar_513_);
v_a_621_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_628_ == 0)
{
v___x_623_ = v___x_600_;
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_600_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_628_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_626_; 
if (v_isShared_624_ == 0)
{
v___x_626_ = v___x_623_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
else
{
v___y_524_ = v___y_514_;
v___y_525_ = v___y_515_;
v___y_526_ = v___y_516_;
v___y_527_ = v___y_517_;
goto v___jp_523_;
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v_a_522_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v_mvar_513_);
v_a_629_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_597_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_597_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
v___jp_523_:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Elab_Tactic_Do_ProofMode_mStart(v_a_522_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_588_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_588_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_588_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_588_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v_proof_x3f_533_; 
v_proof_x3f_533_ = lean_ctor_get(v_a_529_, 1);
if (lean_obj_tag(v_proof_x3f_533_) == 1)
{
lean_object* v_goal_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_574_; 
lean_inc_ref(v_proof_x3f_533_);
lean_del_object(v___x_531_);
v_goal_534_ = lean_ctor_get(v_a_529_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v_a_529_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; 
v_unused_575_ = lean_ctor_get(v_a_529_, 1);
lean_dec(v_unused_575_);
v___x_536_ = v_a_529_;
v_isShared_537_ = v_isSharedCheck_574_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_goal_534_);
lean_dec(v_a_529_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_574_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_val_538_; lean_object* v___x_539_; 
v_val_538_ = lean_ctor_get(v_proof_x3f_533_, 0);
lean_inc(v_val_538_);
lean_dec_ref_known(v_proof_x3f_533_, 1);
lean_inc(v_mvar_513_);
v___x_539_ = l_Lean_MVarId_getTag(v_mvar_513_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
lean_inc_ref(v_goal_534_);
v___x_541_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_534_);
v___x_542_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_541_, v_a_540_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec_ref(v___y_524_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_556_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc_n(v_a_543_, 2);
lean_dec_ref_known(v___x_542_, 1);
v___x_544_ = l_Lean_Expr_app___override(v_val_538_, v_a_543_);
v___x_545_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(v_mvar_513_, v___x_544_, v___y_525_);
lean_dec(v___y_525_);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_556_ == 0)
{
lean_object* v_unused_557_; 
v_unused_557_ = lean_ctor_get(v___x_545_, 0);
lean_dec(v_unused_557_);
v___x_547_ = v___x_545_;
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
else
{
lean_dec(v___x_545_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = l_Lean_Expr_mvarId_x21(v_a_543_);
lean_dec(v_a_543_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v_goal_534_);
lean_ctor_set(v___x_536_, 0, v___x_549_);
v___x_551_ = v___x_536_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_goal_534_);
v___x_551_ = v_reuseFailAlloc_555_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_553_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 0, v___x_551_);
v___x_553_ = v___x_547_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_565_; 
lean_dec(v_val_538_);
lean_del_object(v___x_536_);
lean_dec_ref(v_goal_534_);
lean_dec(v___y_525_);
lean_dec(v_mvar_513_);
v_a_558_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_565_ == 0)
{
v___x_560_ = v___x_542_;
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_542_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_565_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_563_; 
if (v_isShared_561_ == 0)
{
v___x_563_ = v___x_560_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v_a_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_573_; 
lean_dec(v_val_538_);
lean_del_object(v___x_536_);
lean_dec_ref(v_goal_534_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v_mvar_513_);
v_a_566_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_573_ == 0)
{
v___x_568_ = v___x_539_;
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_a_566_);
lean_dec(v___x_539_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_573_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_571_; 
if (v_isShared_569_ == 0)
{
v___x_571_ = v___x_568_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_a_566_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
}
else
{
lean_object* v_goal_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_586_; 
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
v_goal_576_ = lean_ctor_get(v_a_529_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v_a_529_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v_a_529_, 1);
lean_dec(v_unused_587_);
v___x_578_ = v_a_529_;
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_goal_576_);
lean_dec(v_a_529_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v_goal_576_);
lean_ctor_set(v___x_578_, 0, v_mvar_513_);
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_mvar_513_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_goal_576_);
v___x_581_ = v_reuseFailAlloc_585_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; 
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 0, v___x_581_);
v___x_583_ = v___x_531_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
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
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v_mvar_513_);
v_a_589_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_528_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_528_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v_mvar_513_);
v_a_637_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_519_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_519_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___boxed(lean_object* v_mvar_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0(v_mvar_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(lean_object* v_mvar_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v___f_658_; lean_object* v___x_659_; 
lean_inc(v_mvar_652_);
v___f_658_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___lam__0___boxed), 6, 1);
lean_closure_set(v___f_658_, 0, v_mvar_652_);
v___x_659_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__2___redArg(v_mvar_652_, v___f_658_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar___boxed(lean_object* v_mvar_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(v_mvar_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0(lean_object* v_mvarId_667_, lean_object* v_val_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___redArg(v_mvarId_667_, v_val_668_, v___y_670_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0___boxed(lean_object* v_mvarId_675_, lean_object* v_val_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0(v_mvarId_675_, v_val_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1(lean_object* v_00_u03b1_683_, lean_object* v_msg_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___redArg(v_msg_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1___boxed(lean_object* v_00_u03b1_691_, lean_object* v_msg_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1(v_00_u03b1_691_, v_msg_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0(lean_object* v_00_u03b2_699_, lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0___redArg(v_x_700_, v_x_701_, v_x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_704_, lean_object* v_x_705_, size_t v_x_706_, size_t v_x_707_, lean_object* v_x_708_, lean_object* v_x_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___redArg(v_x_705_, v_x_706_, v_x_707_, v_x_708_, v_x_709_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_711_, lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_x_716_){
_start:
{
size_t v_x_3922__boxed_717_; size_t v_x_3923__boxed_718_; lean_object* v_res_719_; 
v_x_3922__boxed_717_ = lean_unbox_usize(v_x_713_);
lean_dec(v_x_713_);
v_x_3923__boxed_718_ = lean_unbox_usize(v_x_714_);
lean_dec(v_x_714_);
v_res_719_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2(v_00_u03b2_711_, v_x_712_, v_x_3922__boxed_717_, v_x_3923__boxed_718_, v_x_715_, v_x_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_720_, lean_object* v_n_721_, lean_object* v_k_722_, lean_object* v_v_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5___redArg(v_n_721_, v_k_722_, v_v_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_725_, size_t v_depth_726_, lean_object* v_keys_727_, lean_object* v_vals_728_, lean_object* v_heq_729_, lean_object* v_i_730_, lean_object* v_entries_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___redArg(v_depth_726_, v_keys_727_, v_vals_728_, v_i_730_, v_entries_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_733_, lean_object* v_depth_734_, lean_object* v_keys_735_, lean_object* v_vals_736_, lean_object* v_heq_737_, lean_object* v_i_738_, lean_object* v_entries_739_){
_start:
{
size_t v_depth_boxed_740_; lean_object* v_res_741_; 
v_depth_boxed_740_ = lean_unbox_usize(v_depth_734_);
lean_dec(v_depth_734_);
v_res_741_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_733_, v_depth_boxed_740_, v_keys_735_, v_vals_736_, v_heq_737_, v_i_738_, v_entries_739_);
lean_dec_ref(v_vals_736_);
lean_dec_ref(v_keys_735_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6(lean_object* v_00_u03b2_742_, lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_, lean_object* v_x_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__0_spec__0_spec__2_spec__5_spec__6___redArg(v_x_743_, v_x_744_, v_x_745_, v_x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref_known(v___x_754_, 1);
v___x_756_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMVar(v_a_755_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
if (lean_obj_tag(v___x_756_) == 0)
{
lean_object* v_a_757_; lean_object* v_fst_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_a_757_ = lean_ctor_get(v___x_756_, 0);
lean_inc(v_a_757_);
lean_dec_ref_known(v___x_756_, 1);
v_fst_758_ = lean_ctor_get(v_a_757_, 0);
v___x_759_ = lean_box(0);
lean_inc(v_fst_758_);
v___x_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_760_, 0, v_fst_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_760_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; 
v_unused_769_ = lean_ctor_get(v___x_761_, 0);
lean_dec(v_unused_769_);
v___x_763_ = v___x_761_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_dec(v___x_761_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 0, v_a_757_);
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_757_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_a_757_);
v_a_770_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_761_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_761_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
else
{
return v___x_756_;
}
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_a_778_ = lean_ctor_get(v___x_754_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_754_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_754_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_754_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg___boxed(lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
lean_dec(v_a_786_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal(lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_794_, v_a_797_, v_a_798_, v_a_799_, v_a_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___boxed(lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal(v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_);
lean_dec(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_box(0);
v___x_820_ = l_Lean_Elab_Tactic_Do_ProofMode_mStartMainGoal___redArg(v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v___x_820_, 0);
lean_dec(v_unused_828_);
v___x_822_ = v___x_820_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_dec(v___x_820_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_819_);
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_819_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_820_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_820_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg___boxed(lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart(lean_object* v_x_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___redArg(v_a_846_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___boxed(lean_object* v_x_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStart(v_x_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_x_855_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1(){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_884_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_885_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__3));
v___x_886_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___closed__6));
v___x_887_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStart___boxed), 10, 0);
v___x_888_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_884_, v___x_885_, v___x_886_, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1___boxed(lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1();
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(lean_object* v_e_891_, lean_object* v___y_892_){
_start:
{
uint8_t v___x_894_; 
v___x_894_ = l_Lean_Expr_hasMVar(v_e_891_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v_e_891_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; lean_object* v_mctx_897_; lean_object* v___x_898_; lean_object* v_fst_899_; lean_object* v_snd_900_; lean_object* v___x_901_; lean_object* v_cache_902_; lean_object* v_zetaDeltaFVarIds_903_; lean_object* v_postponed_904_; lean_object* v_diag_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_914_; 
v___x_896_ = lean_st_ref_get(v___y_892_);
v_mctx_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc_ref(v_mctx_897_);
lean_dec(v___x_896_);
v___x_898_ = l_Lean_instantiateMVarsCore(v_mctx_897_, v_e_891_);
v_fst_899_ = lean_ctor_get(v___x_898_, 0);
lean_inc(v_fst_899_);
v_snd_900_ = lean_ctor_get(v___x_898_, 1);
lean_inc(v_snd_900_);
lean_dec_ref(v___x_898_);
v___x_901_ = lean_st_ref_take(v___y_892_);
v_cache_902_ = lean_ctor_get(v___x_901_, 1);
v_zetaDeltaFVarIds_903_ = lean_ctor_get(v___x_901_, 2);
v_postponed_904_ = lean_ctor_get(v___x_901_, 3);
v_diag_905_ = lean_ctor_get(v___x_901_, 4);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_914_ == 0)
{
lean_object* v_unused_915_; 
v_unused_915_ = lean_ctor_get(v___x_901_, 0);
lean_dec(v_unused_915_);
v___x_907_ = v___x_901_;
v_isShared_908_ = v_isSharedCheck_914_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_diag_905_);
lean_inc(v_postponed_904_);
lean_inc(v_zetaDeltaFVarIds_903_);
lean_inc(v_cache_902_);
lean_dec(v___x_901_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_914_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v_snd_900_);
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_snd_900_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v_cache_902_);
lean_ctor_set(v_reuseFailAlloc_913_, 2, v_zetaDeltaFVarIds_903_);
lean_ctor_set(v_reuseFailAlloc_913_, 3, v_postponed_904_);
lean_ctor_set(v_reuseFailAlloc_913_, 4, v_diag_905_);
v___x_910_ = v_reuseFailAlloc_913_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_st_ref_put(v___y_892_, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v_fst_899_);
return v___x_912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg___boxed(lean_object* v_e_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(v_e_916_, v___y_917_);
lean_dec(v___y_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0(lean_object* v_e_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(v_e_920_, v___y_926_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___boxed(lean_object* v_e_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0(v_e_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0(lean_object* v_x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; 
lean_inc(v___y_946_);
lean_inc_ref(v___y_945_);
lean_inc(v___y_944_);
lean_inc_ref(v___y_943_);
v___x_952_ = lean_apply_9(v_x_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, lean_box(0));
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0___boxed(lean_object* v_x_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0(v_x_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(lean_object* v_mvarId_964_, lean_object* v_x_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___f_975_; lean_object* v___x_976_; 
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
v___f_975_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_975_, 0, v_x_965_);
lean_closure_set(v___f_975_, 1, v___y_966_);
lean_closure_set(v___f_975_, 2, v___y_967_);
lean_closure_set(v___f_975_, 3, v___y_968_);
lean_closure_set(v___f_975_, 4, v___y_969_);
v___x_976_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_964_, v___f_975_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_976_) == 0)
{
return v___x_976_;
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_976_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_976_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg___boxed(lean_object* v_mvarId_985_, lean_object* v_x_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(v_mvarId_985_, v_x_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2(lean_object* v_00_u03b1_997_, lean_object* v_mvarId_998_, lean_object* v_x_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(v_mvarId_998_, v_x_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___boxed(lean_object* v_00_u03b1_1010_, lean_object* v_mvarId_1011_, lean_object* v_x_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2(v_00_u03b1_1010_, v_mvarId_1011_, v_x_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(lean_object* v_msg_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_ref_1029_; lean_object* v___x_1030_; lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1039_; 
v_ref_1029_ = lean_ctor_get(v___y_1026_, 2);
v___x_1030_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mStartMVar_spec__1_spec__2(v_msg_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1033_ = v___x_1030_;
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1030_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
lean_inc(v_ref_1029_);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v_ref_1029_);
lean_ctor_set(v___x_1035_, 1, v_a_1031_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set_tag(v___x_1033_, 1);
lean_ctor_set(v___x_1033_, 0, v___x_1035_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg___boxed(lean_object* v_msg_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(v_msg_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1046_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1048_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__0));
v___x_1049_ = l_Lean_stringToMessageData(v___x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0(lean_object* v_a_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v___x_1060_; 
lean_inc(v_a_1050_);
v___x_1060_ = l_Lean_MVarId_getType(v_a_1050_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; lean_object* v___x_1062_; lean_object* v_a_1063_; lean_object* v___x_1064_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_a_1061_);
lean_dec_ref_known(v___x_1060_, 1);
v___x_1062_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__0___redArg(v_a_1061_, v___y_1056_);
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref(v___x_1062_);
v___x_1064_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_1063_);
lean_dec(v_a_1063_);
if (lean_obj_tag(v___x_1064_) == 1)
{
lean_object* v_val_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_val_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc(v_val_1065_);
lean_dec_ref_known(v___x_1064_, 1);
v___x_1066_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_strip(v_val_1065_);
v___x_1067_ = l_Lean_MVarId_setType___redArg(v_a_1050_, v___x_1066_, v___y_1056_);
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec(v___x_1064_);
lean_dec(v_a_1050_);
v___x_1068_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___closed__1);
v___x_1069_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(v___x_1068_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
return v___x_1069_;
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec(v_a_1050_);
v_a_1070_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1060_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1060_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___boxed(lean_object* v_a_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0(v_a_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_1090_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc_n(v_a_1099_, 2);
lean_dec_ref_known(v___x_1098_, 1);
v___f_1100_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_1100_, 0, v_a_1099_);
v___x_1101_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__2___redArg(v_a_1099_, v___f_1100_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_);
return v___x_1101_;
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_a_1102_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1098_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1098_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg___boxed(lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec(v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec_ref(v_a_1114_);
lean_dec(v_a_1113_);
lean_dec_ref(v_a_1112_);
lean_dec(v_a_1111_);
lean_dec_ref(v_a_1110_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop(lean_object* v_x_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___redArg(v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___boxed(lean_object* v_x_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMStop(v_x_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_);
lean_dec(v_a_1139_);
lean_dec_ref(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec_ref(v_a_1136_);
lean_dec(v_a_1135_);
lean_dec_ref(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_x_1131_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1(lean_object* v_00_u03b1_1142_, lean_object* v_msg_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___redArg(v_msg_1143_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1___boxed(lean_object* v_00_u03b1_1154_, lean_object* v_msg_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMStop_spec__1(v_00_u03b1_1154_, v_msg_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1(){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1181_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_1182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__1));
v___x_1183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___closed__3));
v___x_1184_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMStop___boxed), 10, 0);
v___x_1185_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1181_, v___x_1182_, v___x_1183_, v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1___boxed(lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1();
return v_res_1187_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStart___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStart__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Basic_0__Lean_Elab_Tactic_Do_ProofMode_elabMStop___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMStop__1();
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
