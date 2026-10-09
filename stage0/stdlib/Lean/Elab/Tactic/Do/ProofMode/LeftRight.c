// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.LeftRight
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "target is not SPred.or"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "or_intro_l'"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__6_value),LEAN_SCALAR_PTR_LITERAL(228, 71, 40, 178, 46, 196, 175, 16)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "or_intro_r'"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(88, 44, 62, 183, 159, 188, 9, 155)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not in proof mode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mleft"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(121, 82, 79, 80, 116, 5, 61, 30)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabMLeft"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(121, 20, 10, 20, 51, 143, 96, 253)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mright"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 115, 16, 212, 5, 110, 91, 32)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMRight"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(220, 30, 56, 112, 121, 219, 107, 240)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___boxed(lean_object*);
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_x_46_, lean_object* v_x_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_ks_50_; lean_object* v_vs_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_75_; 
v_ks_50_ = lean_ctor_get(v_x_46_, 0);
v_vs_51_ = lean_ctor_get(v_x_46_, 1);
v_isSharedCheck_75_ = !lean_is_exclusive(v_x_46_);
if (v_isSharedCheck_75_ == 0)
{
v___x_53_ = v_x_46_;
v_isShared_54_ = v_isSharedCheck_75_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_vs_51_);
lean_inc(v_ks_50_);
lean_dec(v_x_46_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_75_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = lean_array_get_size(v_ks_50_);
v___x_56_ = lean_nat_dec_lt(v_x_47_, v___x_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_60_; 
lean_dec(v_x_47_);
v___x_57_ = lean_array_push(v_ks_50_, v_x_48_);
v___x_58_ = lean_array_push(v_vs_51_, v_x_49_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v___x_58_);
lean_ctor_set(v___x_53_, 0, v___x_57_);
v___x_60_ = v___x_53_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_57_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
else
{
lean_object* v_k_x27_62_; uint8_t v___x_63_; 
v_k_x27_62_ = lean_array_fget_borrowed(v_ks_50_, v_x_47_);
v___x_63_ = l_Lean_instBEqMVarId_beq(v_x_48_, v_k_x27_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_65_; 
if (v_isShared_54_ == 0)
{
v___x_65_ = v___x_53_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v_ks_50_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v_vs_51_);
v___x_65_ = v_reuseFailAlloc_69_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(1u);
v___x_67_ = lean_nat_add(v_x_47_, v___x_66_);
lean_dec(v_x_47_);
v_x_46_ = v___x_65_;
v_x_47_ = v___x_67_;
goto _start;
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_70_ = lean_array_fset(v_ks_50_, v_x_47_, v_x_48_);
v___x_71_ = lean_array_fset(v_vs_51_, v_x_47_, v_x_49_);
lean_dec(v_x_47_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 1, v___x_71_);
lean_ctor_set(v___x_53_, 0, v___x_70_);
v___x_73_ = v___x_53_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_70_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_n_76_, lean_object* v_k_77_, lean_object* v_v_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_76_, v___x_79_, v_k_77_, v_v_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_81_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(lean_object* v_x_82_, size_t v_x_83_, size_t v_x_84_, lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v_es_87_; size_t v___x_88_; size_t v___x_89_; lean_object* v_j_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_es_87_ = lean_ctor_get(v_x_82_, 0);
v___x_88_ = ((size_t)31ULL);
v___x_89_ = lean_usize_land(v_x_83_, v___x_88_);
v_j_90_ = lean_usize_to_nat(v___x_89_);
v___x_91_ = lean_array_get_size(v_es_87_);
v___x_92_ = lean_nat_dec_lt(v_j_90_, v___x_91_);
if (v___x_92_ == 0)
{
lean_dec(v_j_90_);
lean_dec(v_x_86_);
lean_dec(v_x_85_);
return v_x_82_;
}
else
{
lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_131_; 
lean_inc_ref(v_es_87_);
v_isSharedCheck_131_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v_x_82_, 0);
lean_dec(v_unused_132_);
v___x_94_ = v_x_82_;
v_isShared_95_ = v_isSharedCheck_131_;
goto v_resetjp_93_;
}
else
{
lean_dec(v_x_82_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_131_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v_v_96_; lean_object* v___x_97_; lean_object* v_xs_x27_98_; lean_object* v___y_100_; 
v_v_96_ = lean_array_fget(v_es_87_, v_j_90_);
v___x_97_ = lean_box(0);
v_xs_x27_98_ = lean_array_fset(v_es_87_, v_j_90_, v___x_97_);
switch(lean_obj_tag(v_v_96_))
{
case 0:
{
lean_object* v_key_105_; lean_object* v_val_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_116_; 
v_key_105_ = lean_ctor_get(v_v_96_, 0);
v_val_106_ = lean_ctor_get(v_v_96_, 1);
v_isSharedCheck_116_ = !lean_is_exclusive(v_v_96_);
if (v_isSharedCheck_116_ == 0)
{
v___x_108_ = v_v_96_;
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_val_106_);
lean_inc(v_key_105_);
lean_dec(v_v_96_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_116_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
uint8_t v___x_110_; 
v___x_110_ = l_Lean_instBEqMVarId_beq(v_x_85_, v_key_105_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_del_object(v___x_108_);
v___x_111_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_105_, v_val_106_, v_x_85_, v_x_86_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
v___y_100_ = v___x_112_;
goto v___jp_99_;
}
else
{
lean_object* v___x_114_; 
lean_dec(v_val_106_);
lean_dec(v_key_105_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v_x_86_);
lean_ctor_set(v___x_108_, 0, v_x_85_);
v___x_114_ = v___x_108_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_x_85_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_x_86_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
v___y_100_ = v___x_114_;
goto v___jp_99_;
}
}
}
}
case 1:
{
lean_object* v_node_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_129_; 
v_node_117_ = lean_ctor_get(v_v_96_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v_v_96_);
if (v_isSharedCheck_129_ == 0)
{
v___x_119_ = v_v_96_;
v_isShared_120_ = v_isSharedCheck_129_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_node_117_);
lean_dec(v_v_96_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_129_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
size_t v___x_121_; size_t v___x_122_; size_t v___x_123_; size_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v___x_121_ = ((size_t)5ULL);
v___x_122_ = lean_usize_shift_right(v_x_83_, v___x_121_);
v___x_123_ = ((size_t)1ULL);
v___x_124_ = lean_usize_add(v_x_84_, v___x_123_);
v___x_125_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_node_117_, v___x_122_, v___x_124_, v_x_85_, v_x_86_);
if (v_isShared_120_ == 0)
{
lean_ctor_set(v___x_119_, 0, v___x_125_);
v___x_127_ = v___x_119_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
v___y_100_ = v___x_127_;
goto v___jp_99_;
}
}
}
default: 
{
lean_object* v___x_130_; 
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v_x_85_);
lean_ctor_set(v___x_130_, 1, v_x_86_);
v___y_100_ = v___x_130_;
goto v___jp_99_;
}
}
v___jp_99_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = lean_array_fset(v_xs_x27_98_, v_j_90_, v___y_100_);
lean_dec(v_j_90_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_101_);
v___x_103_ = v___x_94_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
else
{
lean_object* v_ks_133_; lean_object* v_vs_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_152_; 
v_ks_133_ = lean_ctor_get(v_x_82_, 0);
v_vs_134_ = lean_ctor_get(v_x_82_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_x_82_);
if (v_isSharedCheck_152_ == 0)
{
v___x_136_ = v_x_82_;
v_isShared_137_ = v_isSharedCheck_152_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_vs_134_);
lean_inc(v_ks_133_);
lean_dec(v_x_82_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_152_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_ks_133_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_vs_134_);
v___x_139_ = v_reuseFailAlloc_151_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v_newNode_140_; size_t v___x_141_; uint8_t v___x_142_; 
v_newNode_140_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(v___x_139_, v_x_85_, v_x_86_);
v___x_141_ = ((size_t)7ULL);
v___x_142_ = lean_usize_dec_le(v___x_141_, v_x_84_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_143_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_140_);
v___x_144_ = lean_unsigned_to_nat(4u);
v___x_145_ = lean_nat_dec_lt(v___x_143_, v___x_144_);
lean_dec(v___x_143_);
if (v___x_145_ == 0)
{
lean_object* v_ks_146_; lean_object* v_vs_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_ks_146_ = lean_ctor_get(v_newNode_140_, 0);
lean_inc_ref(v_ks_146_);
v_vs_147_ = lean_ctor_get(v_newNode_140_, 1);
lean_inc_ref(v_vs_147_);
lean_dec_ref(v_newNode_140_);
v___x_148_ = lean_unsigned_to_nat(0u);
v___x_149_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_150_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_x_84_, v_ks_146_, v_vs_147_, v___x_148_, v___x_149_);
lean_dec_ref(v_vs_147_);
lean_dec_ref(v_ks_146_);
return v___x_150_;
}
else
{
return v_newNode_140_;
}
}
else
{
return v_newNode_140_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_82_ = stack[0].m_obj;
size_t v_x_83_ = stack[1].m_num;
size_t v_x_84_ = stack[2].m_num;
lean_object* v_x_85_ = stack[3].m_obj;
lean_object* v_x_86_ = stack[4].m_obj;
lean_object* v_res_153_;
v_res_153_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_82_, v_x_83_, v_x_84_, v_x_85_, v_x_86_);
stack->m_obj
 = v_res_153_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(size_t v_depth_154_, lean_object* v_keys_155_, lean_object* v_vals_156_, lean_object* v_i_157_, lean_object* v_entries_158_){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_array_get_size(v_keys_155_);
v___x_160_ = lean_nat_dec_lt(v_i_157_, v___x_159_);
if (v___x_160_ == 0)
{
lean_dec(v_i_157_);
return v_entries_158_;
}
else
{
lean_object* v_k_161_; lean_object* v_v_162_; uint64_t v___x_163_; size_t v_h_164_; size_t v___x_165_; lean_object* v___x_166_; size_t v___x_167_; size_t v___x_168_; size_t v___x_169_; size_t v_h_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_k_161_ = lean_array_fget_borrowed(v_keys_155_, v_i_157_);
v_v_162_ = lean_array_fget_borrowed(v_vals_156_, v_i_157_);
v___x_163_ = l_Lean_instHashableMVarId_hash(v_k_161_);
v_h_164_ = lean_uint64_to_usize(v___x_163_);
v___x_165_ = ((size_t)5ULL);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = ((size_t)1ULL);
v___x_168_ = lean_usize_sub(v_depth_154_, v___x_167_);
v___x_169_ = lean_usize_mul(v___x_165_, v___x_168_);
v_h_170_ = lean_usize_shift_right(v_h_164_, v___x_169_);
v___x_171_ = lean_nat_add(v_i_157_, v___x_166_);
lean_dec(v_i_157_);
lean_inc(v_v_162_);
lean_inc(v_k_161_);
v___x_172_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_entries_158_, v_h_170_, v_depth_154_, v_k_161_, v_v_162_);
v_i_157_ = v___x_171_;
v_entries_158_ = v___x_172_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_154_ = stack[0].m_num;
lean_object* v_keys_155_ = stack[1].m_obj;
lean_object* v_vals_156_ = stack[2].m_obj;
lean_object* v_i_157_ = stack[3].m_obj;
lean_object* v_entries_158_ = stack[4].m_obj;
lean_object* v_res_174_;
v_res_174_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_154_, v_keys_155_, v_vals_156_, v_i_157_, v_entries_158_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_depth_175_, lean_object* v_keys_176_, lean_object* v_vals_177_, lean_object* v_i_178_, lean_object* v_entries_179_){
_start:
{
size_t v_depth_boxed_180_; lean_object* v_res_181_; 
v_depth_boxed_180_ = lean_unbox_usize(v_depth_175_);
lean_dec(v_depth_175_);
v_res_181_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_180_, v_keys_176_, v_vals_177_, v_i_178_, v_entries_179_);
lean_dec_ref(v_vals_177_);
lean_dec_ref(v_keys_176_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
size_t v_x_3604__boxed_187_; size_t v_x_3605__boxed_188_; lean_object* v_res_189_; 
v_x_3604__boxed_187_ = lean_unbox_usize(v_x_183_);
lean_dec(v_x_183_);
v_x_3605__boxed_188_ = lean_unbox_usize(v_x_184_);
lean_dec(v_x_184_);
v_res_189_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_182_, v_x_3604__boxed_187_, v_x_3605__boxed_188_, v_x_185_, v_x_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
uint64_t v___x_193_; size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; 
v___x_193_ = l_Lean_instHashableMVarId_hash(v_x_191_);
v___x_194_ = lean_uint64_to_usize(v___x_193_);
v___x_195_ = ((size_t)1ULL);
v___x_196_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_190_, v___x_194_, v___x_195_, v_x_191_, v_x_192_);
return v___x_196_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(lean_object* v_mvarId_197_, lean_object* v_val_198_, lean_object* v___y_199_){
_start:
{
lean_object* v___x_201_; lean_object* v_mctx_202_; lean_object* v_cache_203_; lean_object* v_zetaDeltaFVarIds_204_; lean_object* v_postponed_205_; lean_object* v_diag_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_236_; 
v___x_201_ = lean_st_ref_take(v___y_199_);
v_mctx_202_ = lean_ctor_get(v___x_201_, 0);
v_cache_203_ = lean_ctor_get(v___x_201_, 1);
v_zetaDeltaFVarIds_204_ = lean_ctor_get(v___x_201_, 2);
v_postponed_205_ = lean_ctor_get(v___x_201_, 3);
v_diag_206_ = lean_ctor_get(v___x_201_, 4);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_236_ == 0)
{
v___x_208_ = v___x_201_;
v_isShared_209_ = v_isSharedCheck_236_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_diag_206_);
lean_inc(v_postponed_205_);
lean_inc(v_zetaDeltaFVarIds_204_);
lean_inc(v_cache_203_);
lean_inc(v_mctx_202_);
lean_dec(v___x_201_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_236_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_depth_210_; lean_object* v_levelAssignDepth_211_; lean_object* v_lmvarCounter_212_; lean_object* v_mvarCounter_213_; lean_object* v_lDecls_214_; lean_object* v_decls_215_; lean_object* v_userNames_216_; lean_object* v_lAssignment_217_; lean_object* v_eAssignment_218_; lean_object* v_dAssignment_219_; lean_object* v_instanceTypedMVars_220_; lean_object* v_synthNormMemo_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_235_; 
v_depth_210_ = lean_ctor_get(v_mctx_202_, 0);
v_levelAssignDepth_211_ = lean_ctor_get(v_mctx_202_, 1);
v_lmvarCounter_212_ = lean_ctor_get(v_mctx_202_, 2);
v_mvarCounter_213_ = lean_ctor_get(v_mctx_202_, 3);
v_lDecls_214_ = lean_ctor_get(v_mctx_202_, 4);
v_decls_215_ = lean_ctor_get(v_mctx_202_, 5);
v_userNames_216_ = lean_ctor_get(v_mctx_202_, 6);
v_lAssignment_217_ = lean_ctor_get(v_mctx_202_, 7);
v_eAssignment_218_ = lean_ctor_get(v_mctx_202_, 8);
v_dAssignment_219_ = lean_ctor_get(v_mctx_202_, 9);
v_instanceTypedMVars_220_ = lean_ctor_get(v_mctx_202_, 10);
v_synthNormMemo_221_ = lean_ctor_get(v_mctx_202_, 11);
v_isSharedCheck_235_ = !lean_is_exclusive(v_mctx_202_);
if (v_isSharedCheck_235_ == 0)
{
v___x_223_ = v_mctx_202_;
v_isShared_224_ = v_isSharedCheck_235_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_synthNormMemo_221_);
lean_inc(v_instanceTypedMVars_220_);
lean_inc(v_dAssignment_219_);
lean_inc(v_eAssignment_218_);
lean_inc(v_lAssignment_217_);
lean_inc(v_userNames_216_);
lean_inc(v_decls_215_);
lean_inc(v_lDecls_214_);
lean_inc(v_mvarCounter_213_);
lean_inc(v_lmvarCounter_212_);
lean_inc(v_levelAssignDepth_211_);
lean_inc(v_depth_210_);
lean_dec(v_mctx_202_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_235_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_225_ = lean_box(0);
v___x_226_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(v_eAssignment_218_, v_mvarId_197_, v_val_198_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 8, v___x_226_);
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_depth_210_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_levelAssignDepth_211_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_lmvarCounter_212_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_mvarCounter_213_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v_lDecls_214_);
lean_ctor_set(v_reuseFailAlloc_234_, 5, v_decls_215_);
lean_ctor_set(v_reuseFailAlloc_234_, 6, v_userNames_216_);
lean_ctor_set(v_reuseFailAlloc_234_, 7, v_lAssignment_217_);
lean_ctor_set(v_reuseFailAlloc_234_, 8, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_234_, 9, v_dAssignment_219_);
lean_ctor_set(v_reuseFailAlloc_234_, 10, v_instanceTypedMVars_220_);
lean_ctor_set(v_reuseFailAlloc_234_, 11, v_synthNormMemo_221_);
v___x_228_ = v_reuseFailAlloc_234_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_230_; 
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_228_);
v___x_230_ = v___x_208_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_cache_203_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_zetaDeltaFVarIds_204_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v_postponed_205_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v_diag_206_);
v___x_230_ = v_reuseFailAlloc_233_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_st_ref_put(v___y_199_, v___x_230_);
v___x_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_225_);
return v___x_232_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_197_ = stack[0].m_obj;
lean_object* v_val_198_ = stack[1].m_obj;
lean_object* v___y_199_ = stack[2].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(v_mvarId_197_, v_val_198_, v___y_199_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg___boxed(lean_object* v_mvarId_238_, lean_object* v_val_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(v_mvarId_238_, v_val_239_, v___y_240_);
lean_dec(v___y_240_);
return v_res_242_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(lean_object* v_msgData_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; lean_object* v_env_250_; uint8_t v___x_251_; lean_object* v_env_252_; lean_object* v___x_253_; lean_object* v_toCold_254_; lean_object* v_mctx_255_; lean_object* v_lctx_256_; lean_object* v_options_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_249_ = lean_st_ref_get(v___y_247_);
v_env_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc_ref(v_env_250_);
lean_dec(v___x_249_);
v___x_251_ = 0;
v_env_252_ = l_Lean_Environment_setRecordingDeps(v_env_250_, v___x_251_);
v___x_253_ = lean_st_ref_get(v___y_245_);
v_toCold_254_ = lean_ctor_get(v___y_246_, 0);
v_mctx_255_ = lean_ctor_get(v___x_253_, 0);
lean_inc_ref(v_mctx_255_);
lean_dec(v___x_253_);
v_lctx_256_ = lean_ctor_get(v___y_244_, 2);
v_options_257_ = lean_ctor_get(v_toCold_254_, 2);
lean_inc_ref(v_options_257_);
lean_inc_ref(v_lctx_256_);
v___x_258_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_258_, 0, v_env_252_);
lean_ctor_set(v___x_258_, 1, v_mctx_255_);
lean_ctor_set(v___x_258_, 2, v_lctx_256_);
lean_ctor_set(v___x_258_, 3, v_options_257_);
v___x_259_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_msgData_243_);
v___x_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_243_ = stack[0].m_obj;
lean_object* v___y_244_ = stack[1].m_obj;
lean_object* v___y_245_ = stack[2].m_obj;
lean_object* v___y_246_ = stack[3].m_obj;
lean_object* v___y_247_ = stack[4].m_obj;
lean_object* v_res_261_;
v_res_261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(v_msgData_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
stack->m_obj
 = v_res_261_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0___boxed(lean_object* v_msgData_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(v_msgData_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_268_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(lean_object* v_msg_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_ref_275_; lean_object* v___x_276_; lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_285_; 
v_ref_275_ = lean_ctor_get(v___y_272_, 2);
v___x_276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(v_msg_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
v_a_277_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_285_ == 0)
{
v___x_279_ = v___x_276_;
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_276_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_285_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_283_; 
lean_inc(v_ref_275_);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_ref_275_);
lean_ctor_set(v___x_281_, 1, v_a_277_);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 1);
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_283_ = v___x_279_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_269_ = stack[0].m_obj;
lean_object* v___y_270_ = stack[1].m_obj;
lean_object* v___y_271_ = stack[2].m_obj;
lean_object* v___y_272_ = stack[3].m_obj;
lean_object* v___y_273_ = stack[4].m_obj;
lean_object* v_res_286_;
v_res_286_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v_msg_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
stack->m_obj
 = v_res_286_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg___boxed(lean_object* v_msg_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v_msg_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__0));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__10));
v___x_315_ = l_Lean_stringToMessageData(v___x_314_);
return v___x_315_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(uint8_t v_right_316_, lean_object* v_mvar_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v___x_330_; 
lean_inc(v_mvar_317_);
v___x_330_ = l_Lean_MVarId_getType(v_mvar_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_332_; lean_object* v_a_333_; lean_object* v___x_334_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(v_a_331_, v_a_319_);
v_a_333_ = lean_ctor_get(v___x_332_, 0);
lean_inc(v_a_333_);
lean_dec_ref(v___x_332_);
v___x_334_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_333_);
lean_dec(v_a_333_);
if (lean_obj_tag(v___x_334_) == 1)
{
lean_object* v_val_335_; lean_object* v_target_336_; 
v_val_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_val_335_);
lean_dec_ref_known(v___x_334_, 1);
v_target_336_ = lean_ctor_get(v_val_335_, 3);
lean_inc_ref(v_target_336_);
if (lean_obj_tag(v_target_336_) == 5)
{
lean_object* v_fn_337_; 
v_fn_337_ = lean_ctor_get(v_target_336_, 0);
lean_inc_ref(v_fn_337_);
if (lean_obj_tag(v_fn_337_) == 5)
{
lean_object* v_fn_338_; 
v_fn_338_ = lean_ctor_get(v_fn_337_, 0);
lean_inc_ref(v_fn_338_);
if (lean_obj_tag(v_fn_338_) == 5)
{
lean_object* v_fn_339_; 
v_fn_339_ = lean_ctor_get(v_fn_338_, 0);
if (lean_obj_tag(v_fn_339_) == 4)
{
lean_object* v_declName_340_; 
v_declName_340_ = lean_ctor_get(v_fn_339_, 0);
lean_inc(v_declName_340_);
if (lean_obj_tag(v_declName_340_) == 1)
{
lean_object* v_pre_341_; 
v_pre_341_ = lean_ctor_get(v_declName_340_, 0);
lean_inc(v_pre_341_);
if (lean_obj_tag(v_pre_341_) == 1)
{
lean_object* v_pre_342_; 
v_pre_342_ = lean_ctor_get(v_pre_341_, 0);
lean_inc(v_pre_342_);
if (lean_obj_tag(v_pre_342_) == 1)
{
lean_object* v_pre_343_; 
v_pre_343_ = lean_ctor_get(v_pre_342_, 0);
lean_inc(v_pre_343_);
if (lean_obj_tag(v_pre_343_) == 1)
{
lean_object* v_u_344_; lean_object* v_00_u03c3s_345_; lean_object* v_hyps_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_399_; 
v_u_344_ = lean_ctor_get(v_val_335_, 0);
v_00_u03c3s_345_ = lean_ctor_get(v_val_335_, 1);
v_hyps_346_ = lean_ctor_get(v_val_335_, 2);
v_isSharedCheck_399_ = !lean_is_exclusive(v_val_335_);
if (v_isSharedCheck_399_ == 0)
{
lean_object* v_unused_400_; 
v_unused_400_ = lean_ctor_get(v_val_335_, 3);
lean_dec(v_unused_400_);
v___x_348_ = v_val_335_;
v_isShared_349_ = v_isSharedCheck_399_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_hyps_346_);
lean_inc(v_00_u03c3s_345_);
lean_inc(v_u_344_);
lean_dec(v_val_335_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_399_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v_arg_350_; lean_object* v_arg_351_; lean_object* v_arg_352_; lean_object* v_str_353_; lean_object* v_str_354_; lean_object* v_str_355_; lean_object* v_pre_356_; lean_object* v_str_357_; lean_object* v_fst_359_; lean_object* v_snd_360_; 
v_arg_350_ = lean_ctor_get(v_target_336_, 1);
lean_inc_ref(v_arg_350_);
lean_dec_ref_known(v_target_336_, 2);
v_arg_351_ = lean_ctor_get(v_fn_337_, 1);
lean_inc_ref(v_arg_351_);
lean_dec_ref_known(v_fn_337_, 2);
v_arg_352_ = lean_ctor_get(v_fn_338_, 1);
lean_inc_ref(v_arg_352_);
lean_dec_ref_known(v_fn_338_, 2);
v_str_353_ = lean_ctor_get(v_declName_340_, 1);
lean_inc_ref(v_str_353_);
lean_dec_ref_known(v_declName_340_, 2);
v_str_354_ = lean_ctor_get(v_pre_341_, 1);
lean_inc_ref(v_str_354_);
lean_dec_ref_known(v_pre_341_, 2);
v_str_355_ = lean_ctor_get(v_pre_342_, 1);
lean_inc_ref(v_str_355_);
lean_dec_ref_known(v_pre_342_, 2);
v_pre_356_ = lean_ctor_get(v_pre_343_, 0);
lean_inc(v_pre_356_);
v_str_357_ = lean_ctor_get(v_pre_343_, 1);
lean_inc_ref(v_str_357_);
lean_dec_ref_known(v_pre_343_, 2);
if (lean_obj_tag(v_pre_356_) == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2));
v___x_390_ = lean_string_dec_eq(v_str_357_, v___x_389_);
lean_dec_ref(v_str_357_);
if (v___x_390_ == 0)
{
lean_dec_ref(v_str_355_);
lean_dec_ref(v_str_354_);
lean_dec_ref(v_str_353_);
lean_dec_ref(v_arg_352_);
lean_dec_ref(v_arg_351_);
lean_dec_ref(v_arg_350_);
lean_del_object(v___x_348_);
lean_dec_ref(v_hyps_346_);
lean_dec_ref(v_00_u03c3s_345_);
lean_dec(v_u_344_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
else
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3));
v___x_392_ = lean_string_dec_eq(v_str_355_, v___x_391_);
lean_dec_ref(v_str_355_);
if (v___x_392_ == 0)
{
lean_dec_ref(v_str_354_);
lean_dec_ref(v_str_353_);
lean_dec_ref(v_arg_352_);
lean_dec_ref(v_arg_351_);
lean_dec_ref(v_arg_350_);
lean_del_object(v___x_348_);
lean_dec_ref(v_hyps_346_);
lean_dec_ref(v_00_u03c3s_345_);
lean_dec(v_u_344_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
else
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4));
v___x_394_ = lean_string_dec_eq(v_str_354_, v___x_393_);
lean_dec_ref(v_str_354_);
if (v___x_394_ == 0)
{
lean_dec_ref(v_str_353_);
lean_dec_ref(v_arg_352_);
lean_dec_ref(v_arg_351_);
lean_dec_ref(v_arg_350_);
lean_del_object(v___x_348_);
lean_dec_ref(v_hyps_346_);
lean_dec_ref(v_00_u03c3s_345_);
lean_dec(v_u_344_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
else
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__5));
v___x_396_ = lean_string_dec_eq(v_str_353_, v___x_395_);
lean_dec_ref(v_str_353_);
if (v___x_396_ == 0)
{
lean_dec_ref(v_arg_352_);
lean_dec_ref(v_arg_351_);
lean_dec_ref(v_arg_350_);
lean_del_object(v___x_348_);
lean_dec_ref(v_hyps_346_);
lean_dec_ref(v_00_u03c3s_345_);
lean_dec(v_u_344_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
else
{
if (v_right_316_ == 0)
{
lean_object* v___x_397_; 
v___x_397_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7));
lean_inc_ref(v_arg_351_);
v_fst_359_ = v___x_397_;
v_snd_360_ = v_arg_351_;
goto v___jp_358_;
}
else
{
lean_object* v___x_398_; 
v___x_398_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9));
lean_inc_ref(v_arg_350_);
v_fst_359_ = v___x_398_;
v_snd_360_ = v_arg_350_;
goto v___jp_358_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_str_357_);
lean_dec(v_pre_356_);
lean_dec_ref(v_str_355_);
lean_dec_ref(v_str_354_);
lean_dec_ref(v_str_353_);
lean_dec_ref(v_arg_352_);
lean_dec_ref(v_arg_351_);
lean_dec_ref(v_arg_350_);
lean_del_object(v___x_348_);
lean_dec_ref(v_hyps_346_);
lean_dec_ref(v_00_u03c3s_345_);
lean_dec(v_u_344_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
v___jp_358_:
{
lean_object* v___x_362_; 
lean_inc_ref(v_hyps_346_);
lean_inc(v_u_344_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 3, v_snd_360_);
v___x_362_ = v___x_348_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_u_344_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_00_u03c3s_345_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_hyps_346_);
lean_ctor_set(v_reuseFailAlloc_388_, 3, v_snd_360_);
v___x_362_ = v_reuseFailAlloc_388_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_362_);
v___x_364_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_363_, v_pre_356_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_378_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_n(v_a_365_, 2);
lean_dec_ref_known(v___x_364_, 1);
v___x_366_ = lean_box(0);
v___x_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_367_, 0, v_u_344_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
lean_inc(v_fst_359_);
v___x_368_ = l_Lean_mkConst(v_fst_359_, v___x_367_);
v___x_369_ = l_Lean_mkApp5(v___x_368_, v_arg_352_, v_hyps_346_, v_arg_351_, v_arg_350_, v_a_365_);
v___x_370_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(v_mvar_317_, v___x_369_, v_a_319_);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v___x_370_, 0);
lean_dec(v_unused_379_);
v___x_372_ = v___x_370_;
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
else
{
lean_dec(v___x_370_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_378_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = l_Lean_Expr_mvarId_x21(v_a_365_);
lean_dec(v_a_365_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
lean_dec_ref(v_arg_352_);
lean_dec_ref(v_arg_351_);
lean_dec_ref(v_arg_350_);
lean_dec_ref(v_hyps_346_);
lean_dec(v_u_344_);
lean_dec(v_mvar_317_);
v_a_380_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_364_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_364_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_342_, 2);
lean_dec(v_pre_343_);
lean_dec_ref_known(v_pre_341_, 2);
lean_dec_ref_known(v_declName_340_, 2);
lean_dec_ref_known(v_fn_338_, 2);
lean_dec_ref_known(v_fn_337_, 2);
lean_dec_ref_known(v_target_336_, 2);
lean_dec(v_val_335_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
}
else
{
lean_dec(v_pre_342_);
lean_dec_ref_known(v_pre_341_, 2);
lean_dec_ref_known(v_declName_340_, 2);
lean_dec_ref_known(v_fn_338_, 2);
lean_dec_ref_known(v_fn_337_, 2);
lean_dec_ref_known(v_target_336_, 2);
lean_dec(v_val_335_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
}
else
{
lean_dec_ref_known(v_declName_340_, 2);
lean_dec(v_pre_341_);
lean_dec_ref_known(v_fn_338_, 2);
lean_dec_ref_known(v_fn_337_, 2);
lean_dec_ref_known(v_target_336_, 2);
lean_dec(v_val_335_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
}
else
{
lean_dec(v_declName_340_);
lean_dec_ref_known(v_fn_338_, 2);
lean_dec_ref_known(v_fn_337_, 2);
lean_dec_ref_known(v_target_336_, 2);
lean_dec(v_val_335_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
}
else
{
lean_dec_ref_known(v_fn_338_, 2);
lean_dec_ref_known(v_fn_337_, 2);
lean_dec_ref_known(v_target_336_, 2);
lean_dec(v_val_335_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
}
else
{
lean_dec_ref_known(v_fn_337_, 2);
lean_dec_ref(v_fn_338_);
lean_dec_ref_known(v_target_336_, 2);
lean_dec(v_val_335_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
}
else
{
lean_dec_ref_known(v_target_336_, 2);
lean_dec_ref(v_fn_337_);
lean_dec(v_val_335_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
}
else
{
lean_dec_ref(v_target_336_);
lean_dec(v_val_335_);
lean_dec(v_mvar_317_);
v___y_324_ = v_a_318_;
v___y_325_ = v_a_319_;
v___y_326_ = v_a_320_;
v___y_327_ = v_a_321_;
goto v___jp_323_;
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_dec(v___x_334_);
lean_dec(v_mvar_317_);
v___x_401_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11);
v___x_402_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v___x_401_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
return v___x_402_;
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_mvar_317_);
v_a_403_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_330_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_330_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
v___jp_323_:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1);
v___x_329_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v___x_328_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
return v___x_329_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_0interp(lean_interpreter_value* stack)
{
uint8_t v_right_316_ = stack[0].m_num;
lean_object* v_mvar_317_ = stack[1].m_obj;
lean_object* v_a_318_ = stack[2].m_obj;
lean_object* v_a_319_ = stack[3].m_obj;
lean_object* v_a_320_ = stack[4].m_obj;
lean_object* v_a_321_ = stack[5].m_obj;
lean_object* v_res_411_;
v_res_411_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(v_right_316_, v_mvar_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___boxed(lean_object* v_right_412_, lean_object* v_mvar_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
uint8_t v_right_boxed_419_; lean_object* v_res_420_; 
v_right_boxed_419_ = lean_unbox(v_right_412_);
v_res_420_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(v_right_boxed_419_, v_mvar_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
return v_res_420_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0(lean_object* v_00_u03b1_421_, lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
return v___x_428_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_422_ = stack[1].m_obj;
lean_object* v___y_423_ = stack[2].m_obj;
lean_object* v___y_424_ = stack[3].m_obj;
lean_object* v___y_425_ = stack[4].m_obj;
lean_object* v___y_426_ = stack[5].m_obj;
lean_object* v_res_429_;
v_res_429_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0(lean_box(0), v_msg_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___boxed(lean_object* v_00_u03b1_430_, lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0(v_00_u03b1_430_, v_msg_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_437_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2(lean_object* v_mvarId_438_, lean_object* v_val_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(v_mvarId_438_, v_val_439_, v___y_441_);
return v___x_445_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_438_ = stack[0].m_obj;
lean_object* v_val_439_ = stack[1].m_obj;
lean_object* v___y_440_ = stack[2].m_obj;
lean_object* v___y_441_ = stack[3].m_obj;
lean_object* v___y_442_ = stack[4].m_obj;
lean_object* v___y_443_ = stack[5].m_obj;
lean_object* v_res_446_;
v_res_446_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2(v_mvarId_438_, v_val_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
stack->m_obj
 = v_res_446_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___boxed(lean_object* v_mvarId_447_, lean_object* v_val_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2(v_mvarId_447_, v_val_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3(lean_object* v_00_u03b2_455_, lean_object* v_x_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(v_x_456_, v_x_457_, v_x_458_);
return v___x_459_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_460_, lean_object* v_x_461_, size_t v_x_462_, size_t v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_461_, v_x_462_, v_x_463_, v_x_464_, v_x_465_);
return v___x_466_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_461_ = stack[1].m_obj;
size_t v_x_462_ = stack[2].m_num;
size_t v_x_463_ = stack[3].m_num;
lean_object* v_x_464_ = stack[4].m_obj;
lean_object* v_x_465_ = stack[5].m_obj;
lean_object* v_res_467_;
v_res_467_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4(lean_box(0), v_x_461_, v_x_462_, v_x_463_, v_x_464_, v_x_465_);
stack->m_obj
 = v_res_467_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_468_, lean_object* v_x_469_, lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
size_t v_x_4443__boxed_474_; size_t v_x_4444__boxed_475_; lean_object* v_res_476_; 
v_x_4443__boxed_474_ = lean_unbox_usize(v_x_470_);
lean_dec(v_x_470_);
v_x_4444__boxed_475_ = lean_unbox_usize(v_x_471_);
lean_dec(v_x_471_);
v_res_476_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4(v_00_u03b2_468_, v_x_469_, v_x_4443__boxed_474_, v_x_4444__boxed_475_, v_x_472_, v_x_473_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_477_, lean_object* v_n_478_, lean_object* v_k_479_, lean_object* v_v_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(v_n_478_, v_k_479_, v_v_480_);
return v___x_481_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_482_, size_t v_depth_483_, lean_object* v_keys_484_, lean_object* v_vals_485_, lean_object* v_heq_486_, lean_object* v_i_487_, lean_object* v_entries_488_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_483_, v_keys_484_, v_vals_485_, v_i_487_, v_entries_488_);
return v___x_489_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_483_ = stack[1].m_num;
lean_object* v_keys_484_ = stack[2].m_obj;
lean_object* v_vals_485_ = stack[3].m_obj;
lean_object* v_i_487_ = stack[5].m_obj;
lean_object* v_entries_488_ = stack[6].m_obj;
lean_object* v_res_490_;
v_res_490_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6(lean_box(0), v_depth_483_, v_keys_484_, v_vals_485_, lean_box(0), v_i_487_, v_entries_488_);
stack->m_obj
 = v_res_490_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_491_, lean_object* v_depth_492_, lean_object* v_keys_493_, lean_object* v_vals_494_, lean_object* v_heq_495_, lean_object* v_i_496_, lean_object* v_entries_497_){
_start:
{
size_t v_depth_boxed_498_; lean_object* v_res_499_; 
v_depth_boxed_498_ = lean_unbox_usize(v_depth_492_);
lean_dec(v_depth_492_);
v_res_499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_491_, v_depth_boxed_498_, v_keys_493_, v_vals_494_, v_heq_495_, v_i_496_, v_entries_497_);
lean_dec_ref(v_vals_494_);
lean_dec_ref(v_keys_493_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_501_, v_x_502_, v_x_503_, v_x_504_);
return v___x_505_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0(lean_object* v_x_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; 
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
v___x_516_ = lean_apply_9(v_x_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, lean_box(0));
return v___x_516_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_506_ = stack[0].m_obj;
lean_object* v___y_507_ = stack[1].m_obj;
lean_object* v___y_508_ = stack[2].m_obj;
lean_object* v___y_509_ = stack[3].m_obj;
lean_object* v___y_510_ = stack[4].m_obj;
lean_object* v___y_511_ = stack[5].m_obj;
lean_object* v___y_512_ = stack[6].m_obj;
lean_object* v___y_513_ = stack[7].m_obj;
lean_object* v___y_514_ = stack[8].m_obj;
lean_object* v_res_517_;
v_res_517_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0(v_x_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0___boxed(lean_object* v_x_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0(v_x_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_528_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(lean_object* v_mvarId_529_, lean_object* v_x_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_){
_start:
{
lean_object* v___f_540_; lean_object* v___x_541_; 
lean_inc(v___y_534_);
lean_inc_ref(v___y_533_);
lean_inc(v___y_532_);
lean_inc_ref(v___y_531_);
v___f_540_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_540_, 0, v_x_530_);
lean_closure_set(v___f_540_, 1, v___y_531_);
lean_closure_set(v___f_540_, 2, v___y_532_);
lean_closure_set(v___f_540_, 3, v___y_533_);
lean_closure_set(v___f_540_, 4, v___y_534_);
v___x_541_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_529_, v___f_540_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_529_ = stack[0].m_obj;
lean_object* v_x_530_ = stack[1].m_obj;
lean_object* v___y_531_ = stack[2].m_obj;
lean_object* v___y_532_ = stack[3].m_obj;
lean_object* v___y_533_ = stack[4].m_obj;
lean_object* v___y_534_ = stack[5].m_obj;
lean_object* v___y_535_ = stack[6].m_obj;
lean_object* v___y_536_ = stack[7].m_obj;
lean_object* v___y_537_ = stack[8].m_obj;
lean_object* v___y_538_ = stack[9].m_obj;
lean_object* v_res_550_;
v_res_550_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_mvarId_529_, v_x_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
stack->m_obj
 = v_res_550_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___boxed(lean_object* v_mvarId_551_, lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_mvarId_551_, v_x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_562_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0(lean_object* v_00_u03b1_563_, lean_object* v_mvarId_564_, lean_object* v_x_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_mvarId_564_, v_x_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
return v___x_575_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_564_ = stack[1].m_obj;
lean_object* v_x_565_ = stack[2].m_obj;
lean_object* v___y_566_ = stack[3].m_obj;
lean_object* v___y_567_ = stack[4].m_obj;
lean_object* v___y_568_ = stack[5].m_obj;
lean_object* v___y_569_ = stack[6].m_obj;
lean_object* v___y_570_ = stack[7].m_obj;
lean_object* v___y_571_ = stack[8].m_obj;
lean_object* v___y_572_ = stack[9].m_obj;
lean_object* v___y_573_ = stack[10].m_obj;
lean_object* v_res_576_;
v_res_576_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0(lean_box(0), v_mvarId_564_, v_x_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___boxed(lean_object* v_00_u03b1_577_, lean_object* v_mvarId_578_, lean_object* v_x_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0(v_00_u03b1_577_, v_mvarId_578_, v_x_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_589_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0(uint8_t v___x_590_, lean_object* v_a_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(v___x_590_, v_a_591_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v___x_603_ = lean_box(0);
v___x_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_604_, 0, v_a_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_604_, v___y_593_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
return v___x_605_;
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
v_a_606_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_601_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_601_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_590_ = stack[0].m_num;
lean_object* v_a_591_ = stack[1].m_obj;
lean_object* v___y_592_ = stack[2].m_obj;
lean_object* v___y_593_ = stack[3].m_obj;
lean_object* v___y_594_ = stack[4].m_obj;
lean_object* v___y_595_ = stack[5].m_obj;
lean_object* v___y_596_ = stack[6].m_obj;
lean_object* v___y_597_ = stack[7].m_obj;
lean_object* v___y_598_ = stack[8].m_obj;
lean_object* v___y_599_ = stack[9].m_obj;
lean_object* v_res_614_;
v_res_614_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0(v___x_590_, v_a_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
stack->m_obj
 = v_res_614_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed(lean_object* v___x_615_, lean_object* v_a_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
uint8_t v___x_1934__boxed_626_; lean_object* v_res_627_; 
v___x_1934__boxed_626_ = lean_unbox(v___x_615_);
v_res_627_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0(v___x_1934__boxed_626_, v_a_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
return v_res_627_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_629_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; uint8_t v___x_639_; lean_object* v___x_640_; lean_object* v___f_641_; lean_object* v___x_642_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc_n(v_a_638_, 2);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = 0;
v___x_640_ = lean_box(v___x_639_);
v___f_641_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_641_, 0, v___x_640_);
lean_closure_set(v___f_641_, 1, v_a_638_);
v___x_642_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_a_638_, v___f_641_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
return v___x_642_;
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_a_643_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_637_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_637_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_628_ = stack[0].m_obj;
lean_object* v_a_629_ = stack[1].m_obj;
lean_object* v_a_630_ = stack[2].m_obj;
lean_object* v_a_631_ = stack[3].m_obj;
lean_object* v_a_632_ = stack[4].m_obj;
lean_object* v_a_633_ = stack[5].m_obj;
lean_object* v_a_634_ = stack[6].m_obj;
lean_object* v_a_635_ = stack[7].m_obj;
lean_object* v_res_651_;
v_res_651_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
stack->m_obj
 = v_res_651_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___boxed(lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
return v_res_661_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft(lean_object* v_x_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
return v___x_672_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_662_ = stack[0].m_obj;
lean_object* v_a_663_ = stack[1].m_obj;
lean_object* v_a_664_ = stack[2].m_obj;
lean_object* v_a_665_ = stack[3].m_obj;
lean_object* v_a_666_ = stack[4].m_obj;
lean_object* v_a_667_ = stack[5].m_obj;
lean_object* v_a_668_ = stack[6].m_obj;
lean_object* v_a_669_ = stack[7].m_obj;
lean_object* v_a_670_ = stack[8].m_obj;
lean_object* v_res_673_;
v_res_673_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft(v_x_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___boxed(lean_object* v_x_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft(v_x_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_x_674_);
return v_res_684_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1(){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_705_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_706_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4));
v___x_707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8));
v___x_708_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___boxed), 10, 0);
v___x_709_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_705_, v___x_706_, v___x_707_, v___x_708_);
return v___x_709_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_710_;
v_res_710_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1();
stack->m_obj
 = v_res_710_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___boxed(lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1();
return v_res_712_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_714_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___f_726_; lean_object* v___x_727_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
lean_inc_n(v_a_723_, 2);
lean_dec_ref_known(v___x_722_, 1);
v___x_724_ = 1;
v___x_725_ = lean_box(v___x_724_);
v___f_726_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_726_, 0, v___x_725_);
lean_closure_set(v___f_726_, 1, v_a_723_);
v___x_727_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_a_723_, v___f_726_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
return v___x_727_;
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_a_728_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_722_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_722_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_713_ = stack[0].m_obj;
lean_object* v_a_714_ = stack[1].m_obj;
lean_object* v_a_715_ = stack[2].m_obj;
lean_object* v_a_716_ = stack[3].m_obj;
lean_object* v_a_717_ = stack[4].m_obj;
lean_object* v_a_718_ = stack[5].m_obj;
lean_object* v_a_719_ = stack[6].m_obj;
lean_object* v_a_720_ = stack[7].m_obj;
lean_object* v_res_736_;
v_res_736_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
stack->m_obj
 = v_res_736_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg___boxed(lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
return v_res_746_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight(lean_object* v_x_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
return v___x_757_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMRight_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_747_ = stack[0].m_obj;
lean_object* v_a_748_ = stack[1].m_obj;
lean_object* v_a_749_ = stack[2].m_obj;
lean_object* v_a_750_ = stack[3].m_obj;
lean_object* v_a_751_ = stack[4].m_obj;
lean_object* v_a_752_ = stack[5].m_obj;
lean_object* v_a_753_ = stack[6].m_obj;
lean_object* v_a_754_ = stack[7].m_obj;
lean_object* v_a_755_ = stack[8].m_obj;
lean_object* v_res_758_;
v_res_758_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight(v_x_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___boxed(lean_object* v_x_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight(v_x_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec_ref(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_x_759_);
return v_res_769_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1(){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_785_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_786_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1));
v___x_787_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3));
v___x_788_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___boxed), 10, 0);
v___x_789_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_785_, v___x_786_, v___x_787_, v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_790_;
v_res_790_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1();
stack->m_obj
 = v_res_790_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___boxed(lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1();
return v_res_792_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(uint8_t builtin) {
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
res = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(builtin);
}
#ifdef __cplusplus
}
#endif
