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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(v_e_30_, v___y_32_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1(v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_x_44_, lean_object* v_x_45_, lean_object* v_x_46_, lean_object* v_x_47_){
_start:
{
lean_object* v_ks_48_; lean_object* v_vs_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_73_; 
v_ks_48_ = lean_ctor_get(v_x_44_, 0);
v_vs_49_ = lean_ctor_get(v_x_44_, 1);
v_isSharedCheck_73_ = !lean_is_exclusive(v_x_44_);
if (v_isSharedCheck_73_ == 0)
{
v___x_51_ = v_x_44_;
v_isShared_52_ = v_isSharedCheck_73_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_vs_49_);
lean_inc(v_ks_48_);
lean_dec(v_x_44_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_73_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; uint8_t v___x_54_; 
v___x_53_ = lean_array_get_size(v_ks_48_);
v___x_54_ = lean_nat_dec_lt(v_x_45_, v___x_53_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_58_; 
lean_dec(v_x_45_);
v___x_55_ = lean_array_push(v_ks_48_, v_x_46_);
v___x_56_ = lean_array_push(v_vs_49_, v_x_47_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___x_56_);
lean_ctor_set(v___x_51_, 0, v___x_55_);
v___x_58_ = v___x_51_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_55_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
else
{
lean_object* v_k_x27_60_; uint8_t v___x_61_; 
v_k_x27_60_ = lean_array_fget_borrowed(v_ks_48_, v_x_45_);
v___x_61_ = l_Lean_instBEqMVarId_beq(v_x_46_, v_k_x27_60_);
if (v___x_61_ == 0)
{
lean_object* v___x_63_; 
if (v_isShared_52_ == 0)
{
v___x_63_ = v___x_51_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_ks_48_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v_vs_49_);
v___x_63_ = v_reuseFailAlloc_67_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v___x_65_ = lean_nat_add(v_x_45_, v___x_64_);
lean_dec(v_x_45_);
v_x_44_ = v___x_63_;
v_x_45_ = v___x_65_;
goto _start;
}
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_68_ = lean_array_fset(v_ks_48_, v_x_45_, v_x_46_);
v___x_69_ = lean_array_fset(v_vs_49_, v_x_45_, v_x_47_);
lean_dec(v_x_45_);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___x_69_);
lean_ctor_set(v___x_51_, 0, v___x_68_);
v___x_71_ = v___x_51_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
return v___x_71_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_n_74_, lean_object* v_k_75_, lean_object* v_v_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_74_, v___x_77_, v_k_75_, v_v_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(lean_object* v_x_80_, size_t v_x_81_, size_t v_x_82_, lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
if (lean_obj_tag(v_x_80_) == 0)
{
lean_object* v_es_85_; size_t v___x_86_; size_t v___x_87_; lean_object* v_j_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_es_85_ = lean_ctor_get(v_x_80_, 0);
v___x_86_ = ((size_t)31ULL);
v___x_87_ = lean_usize_land(v_x_81_, v___x_86_);
v_j_88_ = lean_usize_to_nat(v___x_87_);
v___x_89_ = lean_array_get_size(v_es_85_);
v___x_90_ = lean_nat_dec_lt(v_j_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_dec(v_j_88_);
lean_dec(v_x_84_);
lean_dec(v_x_83_);
return v_x_80_;
}
else
{
lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_129_; 
lean_inc_ref(v_es_85_);
v_isSharedCheck_129_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; 
v_unused_130_ = lean_ctor_get(v_x_80_, 0);
lean_dec(v_unused_130_);
v___x_92_ = v_x_80_;
v_isShared_93_ = v_isSharedCheck_129_;
goto v_resetjp_91_;
}
else
{
lean_dec(v_x_80_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_129_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v_v_94_; lean_object* v___x_95_; lean_object* v_xs_x27_96_; lean_object* v___y_98_; 
v_v_94_ = lean_array_fget(v_es_85_, v_j_88_);
v___x_95_ = lean_box(0);
v_xs_x27_96_ = lean_array_fset(v_es_85_, v_j_88_, v___x_95_);
switch(lean_obj_tag(v_v_94_))
{
case 0:
{
lean_object* v_key_103_; lean_object* v_val_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_114_; 
v_key_103_ = lean_ctor_get(v_v_94_, 0);
v_val_104_ = lean_ctor_get(v_v_94_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v_v_94_);
if (v_isSharedCheck_114_ == 0)
{
v___x_106_ = v_v_94_;
v_isShared_107_ = v_isSharedCheck_114_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_val_104_);
lean_inc(v_key_103_);
lean_dec(v_v_94_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_114_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
uint8_t v___x_108_; 
v___x_108_ = l_Lean_instBEqMVarId_beq(v_x_83_, v_key_103_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_del_object(v___x_106_);
v___x_109_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_103_, v_val_104_, v_x_83_, v_x_84_);
v___x_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
v___y_98_ = v___x_110_;
goto v___jp_97_;
}
else
{
lean_object* v___x_112_; 
lean_dec(v_val_104_);
lean_dec(v_key_103_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v_x_84_);
lean_ctor_set(v___x_106_, 0, v_x_83_);
v___x_112_ = v___x_106_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_x_83_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_x_84_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
v___y_98_ = v___x_112_;
goto v___jp_97_;
}
}
}
}
case 1:
{
lean_object* v_node_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_127_; 
v_node_115_ = lean_ctor_get(v_v_94_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v_v_94_);
if (v_isSharedCheck_127_ == 0)
{
v___x_117_ = v_v_94_;
v_isShared_118_ = v_isSharedCheck_127_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_node_115_);
lean_dec(v_v_94_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_127_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
size_t v___x_119_; size_t v___x_120_; size_t v___x_121_; size_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_119_ = ((size_t)5ULL);
v___x_120_ = lean_usize_shift_right(v_x_81_, v___x_119_);
v___x_121_ = ((size_t)1ULL);
v___x_122_ = lean_usize_add(v_x_82_, v___x_121_);
v___x_123_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_node_115_, v___x_120_, v___x_122_, v_x_83_, v_x_84_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_123_);
v___x_125_ = v___x_117_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_123_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
v___y_98_ = v___x_125_;
goto v___jp_97_;
}
}
}
default: 
{
lean_object* v___x_128_; 
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v_x_83_);
lean_ctor_set(v___x_128_, 1, v_x_84_);
v___y_98_ = v___x_128_;
goto v___jp_97_;
}
}
v___jp_97_:
{
lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_99_ = lean_array_fset(v_xs_x27_96_, v_j_88_, v___y_98_);
lean_dec(v_j_88_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_99_);
v___x_101_ = v___x_92_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
}
else
{
lean_object* v_ks_131_; lean_object* v_vs_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_152_; 
v_ks_131_ = lean_ctor_get(v_x_80_, 0);
v_vs_132_ = lean_ctor_get(v_x_80_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_x_80_);
if (v_isSharedCheck_152_ == 0)
{
v___x_134_ = v_x_80_;
v_isShared_135_ = v_isSharedCheck_152_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_vs_132_);
lean_inc(v_ks_131_);
lean_dec(v_x_80_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_152_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_ks_131_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v_vs_132_);
v___x_137_ = v_reuseFailAlloc_151_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v_newNode_138_; uint8_t v___y_140_; size_t v___x_146_; uint8_t v___x_147_; 
v_newNode_138_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(v___x_137_, v_x_83_, v_x_84_);
v___x_146_ = ((size_t)7ULL);
v___x_147_ = lean_usize_dec_le(v___x_146_, v_x_82_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_148_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_138_);
v___x_149_ = lean_unsigned_to_nat(4u);
v___x_150_ = lean_nat_dec_lt(v___x_148_, v___x_149_);
lean_dec(v___x_148_);
v___y_140_ = v___x_150_;
goto v___jp_139_;
}
else
{
v___y_140_ = v___x_147_;
goto v___jp_139_;
}
v___jp_139_:
{
if (v___y_140_ == 0)
{
lean_object* v_ks_141_; lean_object* v_vs_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_ks_141_ = lean_ctor_get(v_newNode_138_, 0);
lean_inc_ref(v_ks_141_);
v_vs_142_ = lean_ctor_get(v_newNode_138_, 1);
lean_inc_ref(v_vs_142_);
lean_dec_ref(v_newNode_138_);
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_145_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_x_82_, v_ks_141_, v_vs_142_, v___x_143_, v___x_144_);
lean_dec_ref(v_vs_142_);
lean_dec_ref(v_ks_141_);
return v___x_145_;
}
else
{
return v_newNode_138_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(size_t v_depth_153_, lean_object* v_keys_154_, lean_object* v_vals_155_, lean_object* v_i_156_, lean_object* v_entries_157_){
_start:
{
lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_158_ = lean_array_get_size(v_keys_154_);
v___x_159_ = lean_nat_dec_lt(v_i_156_, v___x_158_);
if (v___x_159_ == 0)
{
lean_dec(v_i_156_);
return v_entries_157_;
}
else
{
lean_object* v_k_160_; lean_object* v_v_161_; uint64_t v___x_162_; size_t v_h_163_; size_t v___x_164_; lean_object* v___x_165_; size_t v___x_166_; size_t v___x_167_; size_t v___x_168_; size_t v_h_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_k_160_ = lean_array_fget_borrowed(v_keys_154_, v_i_156_);
v_v_161_ = lean_array_fget_borrowed(v_vals_155_, v_i_156_);
v___x_162_ = l_Lean_instHashableMVarId_hash(v_k_160_);
v_h_163_ = lean_uint64_to_usize(v___x_162_);
v___x_164_ = ((size_t)5ULL);
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = ((size_t)1ULL);
v___x_167_ = lean_usize_sub(v_depth_153_, v___x_166_);
v___x_168_ = lean_usize_mul(v___x_164_, v___x_167_);
v_h_169_ = lean_usize_shift_right(v_h_163_, v___x_168_);
v___x_170_ = lean_nat_add(v_i_156_, v___x_165_);
lean_dec(v_i_156_);
lean_inc(v_v_161_);
lean_inc(v_k_160_);
v___x_171_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_entries_157_, v_h_169_, v_depth_153_, v_k_160_, v_v_161_);
v_i_156_ = v___x_170_;
v_entries_157_ = v___x_171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_depth_173_, lean_object* v_keys_174_, lean_object* v_vals_175_, lean_object* v_i_176_, lean_object* v_entries_177_){
_start:
{
size_t v_depth_boxed_178_; lean_object* v_res_179_; 
v_depth_boxed_178_ = lean_unbox_usize(v_depth_173_);
lean_dec(v_depth_173_);
v_res_179_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_178_, v_keys_174_, v_vals_175_, v_i_176_, v_entries_177_);
lean_dec_ref(v_vals_175_);
lean_dec_ref(v_keys_174_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_180_, lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
size_t v_x_3562__boxed_185_; size_t v_x_3563__boxed_186_; lean_object* v_res_187_; 
v_x_3562__boxed_185_ = lean_unbox_usize(v_x_181_);
lean_dec(v_x_181_);
v_x_3563__boxed_186_ = lean_unbox_usize(v_x_182_);
lean_dec(v_x_182_);
v_res_187_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_180_, v_x_3562__boxed_185_, v_x_3563__boxed_186_, v_x_183_, v_x_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
uint64_t v___x_191_; size_t v___x_192_; size_t v___x_193_; lean_object* v___x_194_; 
v___x_191_ = l_Lean_instHashableMVarId_hash(v_x_189_);
v___x_192_ = lean_uint64_to_usize(v___x_191_);
v___x_193_ = ((size_t)1ULL);
v___x_194_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_188_, v___x_192_, v___x_193_, v_x_189_, v_x_190_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(lean_object* v_mvarId_195_, lean_object* v_val_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v_mctx_200_; lean_object* v_cache_201_; lean_object* v_zetaDeltaFVarIds_202_; lean_object* v_postponed_203_; lean_object* v_diag_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_233_; 
v___x_199_ = lean_st_ref_take(v___y_197_);
v_mctx_200_ = lean_ctor_get(v___x_199_, 0);
v_cache_201_ = lean_ctor_get(v___x_199_, 1);
v_zetaDeltaFVarIds_202_ = lean_ctor_get(v___x_199_, 2);
v_postponed_203_ = lean_ctor_get(v___x_199_, 3);
v_diag_204_ = lean_ctor_get(v___x_199_, 4);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_233_ == 0)
{
v___x_206_ = v___x_199_;
v_isShared_207_ = v_isSharedCheck_233_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_diag_204_);
lean_inc(v_postponed_203_);
lean_inc(v_zetaDeltaFVarIds_202_);
lean_inc(v_cache_201_);
lean_inc(v_mctx_200_);
lean_dec(v___x_199_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_233_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v_depth_208_; lean_object* v_levelAssignDepth_209_; lean_object* v_lmvarCounter_210_; lean_object* v_mvarCounter_211_; lean_object* v_lDecls_212_; lean_object* v_decls_213_; lean_object* v_userNames_214_; lean_object* v_lAssignment_215_; lean_object* v_eAssignment_216_; lean_object* v_dAssignment_217_; lean_object* v_instanceTypedMVars_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_232_; 
v_depth_208_ = lean_ctor_get(v_mctx_200_, 0);
v_levelAssignDepth_209_ = lean_ctor_get(v_mctx_200_, 1);
v_lmvarCounter_210_ = lean_ctor_get(v_mctx_200_, 2);
v_mvarCounter_211_ = lean_ctor_get(v_mctx_200_, 3);
v_lDecls_212_ = lean_ctor_get(v_mctx_200_, 4);
v_decls_213_ = lean_ctor_get(v_mctx_200_, 5);
v_userNames_214_ = lean_ctor_get(v_mctx_200_, 6);
v_lAssignment_215_ = lean_ctor_get(v_mctx_200_, 7);
v_eAssignment_216_ = lean_ctor_get(v_mctx_200_, 8);
v_dAssignment_217_ = lean_ctor_get(v_mctx_200_, 9);
v_instanceTypedMVars_218_ = lean_ctor_get(v_mctx_200_, 10);
v_isSharedCheck_232_ = !lean_is_exclusive(v_mctx_200_);
if (v_isSharedCheck_232_ == 0)
{
v___x_220_ = v_mctx_200_;
v_isShared_221_ = v_isSharedCheck_232_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_instanceTypedMVars_218_);
lean_inc(v_dAssignment_217_);
lean_inc(v_eAssignment_216_);
lean_inc(v_lAssignment_215_);
lean_inc(v_userNames_214_);
lean_inc(v_decls_213_);
lean_inc(v_lDecls_212_);
lean_inc(v_mvarCounter_211_);
lean_inc(v_lmvarCounter_210_);
lean_inc(v_levelAssignDepth_209_);
lean_inc(v_depth_208_);
lean_dec(v_mctx_200_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_232_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(v_eAssignment_216_, v_mvarId_195_, v_val_196_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 8, v___x_222_);
v___x_224_ = v___x_220_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_depth_208_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_levelAssignDepth_209_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_lmvarCounter_210_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_mvarCounter_211_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_lDecls_212_);
lean_ctor_set(v_reuseFailAlloc_231_, 5, v_decls_213_);
lean_ctor_set(v_reuseFailAlloc_231_, 6, v_userNames_214_);
lean_ctor_set(v_reuseFailAlloc_231_, 7, v_lAssignment_215_);
lean_ctor_set(v_reuseFailAlloc_231_, 8, v___x_222_);
lean_ctor_set(v_reuseFailAlloc_231_, 9, v_dAssignment_217_);
lean_ctor_set(v_reuseFailAlloc_231_, 10, v_instanceTypedMVars_218_);
v___x_224_ = v_reuseFailAlloc_231_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_226_; 
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_224_);
v___x_226_ = v___x_206_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_cache_201_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_zetaDeltaFVarIds_202_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_postponed_203_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_diag_204_);
v___x_226_ = v_reuseFailAlloc_230_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_st_ref_put(v___y_197_, v___x_226_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg___boxed(lean_object* v_mvarId_234_, lean_object* v_val_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(v_mvarId_234_, v_val_235_, v___y_236_);
lean_dec(v___y_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(lean_object* v_msgData_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; lean_object* v_env_246_; lean_object* v___x_247_; lean_object* v_mctx_248_; lean_object* v_lctx_249_; lean_object* v_options_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_245_ = lean_st_ref_get(v___y_243_);
v_env_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc_ref(v_env_246_);
lean_dec(v___x_245_);
v___x_247_ = lean_st_ref_get(v___y_241_);
v_mctx_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc_ref(v_mctx_248_);
lean_dec(v___x_247_);
v_lctx_249_ = lean_ctor_get(v___y_240_, 2);
v_options_250_ = lean_ctor_get(v___y_242_, 2);
lean_inc_ref(v_options_250_);
lean_inc_ref(v_lctx_249_);
v___x_251_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_251_, 0, v_env_246_);
lean_ctor_set(v___x_251_, 1, v_mctx_248_);
lean_ctor_set(v___x_251_, 2, v_lctx_249_);
lean_ctor_set(v___x_251_, 3, v_options_250_);
v___x_252_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v_msgData_239_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0___boxed(lean_object* v_msgData_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(v_msgData_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_ref_267_; lean_object* v___x_268_; lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_ref_267_ = lean_ctor_get(v___y_264_, 5);
v___x_268_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(v_msg_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
lean_inc(v_ref_267_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_ref_267_);
lean_ctor_set(v___x_273_, 1, v_a_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 1);
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg___boxed(lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v_msg_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_284_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__0));
v___x_287_ = l_Lean_stringToMessageData(v___x_286_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__10));
v___x_306_ = l_Lean_stringToMessageData(v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(uint8_t v_right_307_, lean_object* v_mvar_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___x_321_; 
lean_inc(v_mvar_308_);
v___x_321_ = l_Lean_MVarId_getType(v_mvar_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; lean_object* v___x_323_; lean_object* v_a_324_; lean_object* v___x_325_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(v_a_322_, v_a_310_);
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref(v___x_323_);
v___x_325_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_324_);
lean_dec(v_a_324_);
if (lean_obj_tag(v___x_325_) == 1)
{
lean_object* v_val_326_; lean_object* v_target_327_; 
v_val_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_val_326_);
lean_dec_ref_known(v___x_325_, 1);
v_target_327_ = lean_ctor_get(v_val_326_, 3);
lean_inc_ref(v_target_327_);
if (lean_obj_tag(v_target_327_) == 5)
{
lean_object* v_fn_328_; 
v_fn_328_ = lean_ctor_get(v_target_327_, 0);
lean_inc_ref(v_fn_328_);
if (lean_obj_tag(v_fn_328_) == 5)
{
lean_object* v_fn_329_; 
v_fn_329_ = lean_ctor_get(v_fn_328_, 0);
lean_inc_ref(v_fn_329_);
if (lean_obj_tag(v_fn_329_) == 5)
{
lean_object* v_fn_330_; 
v_fn_330_ = lean_ctor_get(v_fn_329_, 0);
if (lean_obj_tag(v_fn_330_) == 4)
{
lean_object* v_declName_331_; 
v_declName_331_ = lean_ctor_get(v_fn_330_, 0);
lean_inc(v_declName_331_);
if (lean_obj_tag(v_declName_331_) == 1)
{
lean_object* v_pre_332_; 
v_pre_332_ = lean_ctor_get(v_declName_331_, 0);
lean_inc(v_pre_332_);
if (lean_obj_tag(v_pre_332_) == 1)
{
lean_object* v_pre_333_; 
v_pre_333_ = lean_ctor_get(v_pre_332_, 0);
lean_inc(v_pre_333_);
if (lean_obj_tag(v_pre_333_) == 1)
{
lean_object* v_pre_334_; 
v_pre_334_ = lean_ctor_get(v_pre_333_, 0);
lean_inc(v_pre_334_);
if (lean_obj_tag(v_pre_334_) == 1)
{
lean_object* v_u_335_; lean_object* v_00_u03c3s_336_; lean_object* v_hyps_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_390_; 
v_u_335_ = lean_ctor_get(v_val_326_, 0);
v_00_u03c3s_336_ = lean_ctor_get(v_val_326_, 1);
v_hyps_337_ = lean_ctor_get(v_val_326_, 2);
v_isSharedCheck_390_ = !lean_is_exclusive(v_val_326_);
if (v_isSharedCheck_390_ == 0)
{
lean_object* v_unused_391_; 
v_unused_391_ = lean_ctor_get(v_val_326_, 3);
lean_dec(v_unused_391_);
v___x_339_ = v_val_326_;
v_isShared_340_ = v_isSharedCheck_390_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_hyps_337_);
lean_inc(v_00_u03c3s_336_);
lean_inc(v_u_335_);
lean_dec(v_val_326_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_390_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v_arg_341_; lean_object* v_arg_342_; lean_object* v_arg_343_; lean_object* v_str_344_; lean_object* v_str_345_; lean_object* v_str_346_; lean_object* v_pre_347_; lean_object* v_str_348_; lean_object* v_fst_350_; lean_object* v_snd_351_; 
v_arg_341_ = lean_ctor_get(v_target_327_, 1);
lean_inc_ref(v_arg_341_);
lean_dec_ref_known(v_target_327_, 2);
v_arg_342_ = lean_ctor_get(v_fn_328_, 1);
lean_inc_ref(v_arg_342_);
lean_dec_ref_known(v_fn_328_, 2);
v_arg_343_ = lean_ctor_get(v_fn_329_, 1);
lean_inc_ref(v_arg_343_);
lean_dec_ref_known(v_fn_329_, 2);
v_str_344_ = lean_ctor_get(v_declName_331_, 1);
lean_inc_ref(v_str_344_);
lean_dec_ref_known(v_declName_331_, 2);
v_str_345_ = lean_ctor_get(v_pre_332_, 1);
lean_inc_ref(v_str_345_);
lean_dec_ref_known(v_pre_332_, 2);
v_str_346_ = lean_ctor_get(v_pre_333_, 1);
lean_inc_ref(v_str_346_);
lean_dec_ref_known(v_pre_333_, 2);
v_pre_347_ = lean_ctor_get(v_pre_334_, 0);
lean_inc(v_pre_347_);
v_str_348_ = lean_ctor_get(v_pre_334_, 1);
lean_inc_ref(v_str_348_);
lean_dec_ref_known(v_pre_334_, 2);
if (lean_obj_tag(v_pre_347_) == 0)
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2));
v___x_381_ = lean_string_dec_eq(v_str_348_, v___x_380_);
lean_dec_ref(v_str_348_);
if (v___x_381_ == 0)
{
lean_dec_ref(v_str_346_);
lean_dec_ref(v_str_345_);
lean_dec_ref(v_str_344_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_341_);
lean_del_object(v___x_339_);
lean_dec_ref(v_hyps_337_);
lean_dec_ref(v_00_u03c3s_336_);
lean_dec(v_u_335_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
else
{
lean_object* v___x_382_; uint8_t v___x_383_; 
v___x_382_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3));
v___x_383_ = lean_string_dec_eq(v_str_346_, v___x_382_);
lean_dec_ref(v_str_346_);
if (v___x_383_ == 0)
{
lean_dec_ref(v_str_345_);
lean_dec_ref(v_str_344_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_341_);
lean_del_object(v___x_339_);
lean_dec_ref(v_hyps_337_);
lean_dec_ref(v_00_u03c3s_336_);
lean_dec(v_u_335_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
else
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4));
v___x_385_ = lean_string_dec_eq(v_str_345_, v___x_384_);
lean_dec_ref(v_str_345_);
if (v___x_385_ == 0)
{
lean_dec_ref(v_str_344_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_341_);
lean_del_object(v___x_339_);
lean_dec_ref(v_hyps_337_);
lean_dec_ref(v_00_u03c3s_336_);
lean_dec(v_u_335_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
else
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__5));
v___x_387_ = lean_string_dec_eq(v_str_344_, v___x_386_);
lean_dec_ref(v_str_344_);
if (v___x_387_ == 0)
{
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_341_);
lean_del_object(v___x_339_);
lean_dec_ref(v_hyps_337_);
lean_dec_ref(v_00_u03c3s_336_);
lean_dec(v_u_335_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
else
{
if (v_right_307_ == 0)
{
lean_object* v___x_388_; 
v___x_388_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7));
lean_inc_ref(v_arg_342_);
v_fst_350_ = v___x_388_;
v_snd_351_ = v_arg_342_;
goto v___jp_349_;
}
else
{
lean_object* v___x_389_; 
v___x_389_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9));
lean_inc_ref(v_arg_341_);
v_fst_350_ = v___x_389_;
v_snd_351_ = v_arg_341_;
goto v___jp_349_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_str_348_);
lean_dec(v_pre_347_);
lean_dec_ref(v_str_346_);
lean_dec_ref(v_str_345_);
lean_dec_ref(v_str_344_);
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_341_);
lean_del_object(v___x_339_);
lean_dec_ref(v_hyps_337_);
lean_dec_ref(v_00_u03c3s_336_);
lean_dec(v_u_335_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
v___jp_349_:
{
lean_object* v___x_353_; 
lean_inc_ref(v_hyps_337_);
lean_inc(v_u_335_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 3, v_snd_351_);
v___x_353_ = v___x_339_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_u_335_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_00_u03c3s_336_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_hyps_337_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v_snd_351_);
v___x_353_ = v_reuseFailAlloc_379_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_353_);
v___x_355_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_354_, v_pre_347_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_369_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc_n(v_a_356_, 2);
lean_dec_ref_known(v___x_355_, 1);
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_358_, 0, v_u_335_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
lean_inc(v_fst_350_);
v___x_359_ = l_Lean_mkConst(v_fst_350_, v___x_358_);
v___x_360_ = l_Lean_mkApp5(v___x_359_, v_arg_343_, v_hyps_337_, v_arg_342_, v_arg_341_, v_a_356_);
v___x_361_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(v_mvar_308_, v___x_360_, v_a_310_);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_369_ == 0)
{
lean_object* v_unused_370_; 
v_unused_370_ = lean_ctor_get(v___x_361_, 0);
lean_dec(v_unused_370_);
v___x_363_ = v___x_361_;
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
else
{
lean_dec(v___x_361_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = l_Lean_Expr_mvarId_x21(v_a_356_);
lean_dec(v_a_356_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_dec_ref(v_arg_343_);
lean_dec_ref(v_arg_342_);
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_hyps_337_);
lean_dec(v_u_335_);
lean_dec(v_mvar_308_);
v_a_371_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_355_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_355_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_333_, 2);
lean_dec(v_pre_334_);
lean_dec_ref_known(v_pre_332_, 2);
lean_dec_ref_known(v_declName_331_, 2);
lean_dec_ref_known(v_fn_329_, 2);
lean_dec_ref_known(v_fn_328_, 2);
lean_dec_ref_known(v_target_327_, 2);
lean_dec(v_val_326_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
}
else
{
lean_dec(v_pre_333_);
lean_dec_ref_known(v_pre_332_, 2);
lean_dec_ref_known(v_declName_331_, 2);
lean_dec_ref_known(v_fn_329_, 2);
lean_dec_ref_known(v_fn_328_, 2);
lean_dec_ref_known(v_target_327_, 2);
lean_dec(v_val_326_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
}
else
{
lean_dec(v_pre_332_);
lean_dec_ref_known(v_declName_331_, 2);
lean_dec_ref_known(v_fn_329_, 2);
lean_dec_ref_known(v_fn_328_, 2);
lean_dec_ref_known(v_target_327_, 2);
lean_dec(v_val_326_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
}
else
{
lean_dec(v_declName_331_);
lean_dec_ref_known(v_fn_329_, 2);
lean_dec_ref_known(v_fn_328_, 2);
lean_dec_ref_known(v_target_327_, 2);
lean_dec(v_val_326_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
}
else
{
lean_dec_ref_known(v_fn_329_, 2);
lean_dec_ref_known(v_fn_328_, 2);
lean_dec_ref_known(v_target_327_, 2);
lean_dec(v_val_326_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
}
else
{
lean_dec_ref(v_fn_329_);
lean_dec_ref_known(v_fn_328_, 2);
lean_dec_ref_known(v_target_327_, 2);
lean_dec(v_val_326_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
}
else
{
lean_dec_ref_known(v_target_327_, 2);
lean_dec_ref(v_fn_328_);
lean_dec(v_val_326_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
}
else
{
lean_dec_ref(v_target_327_);
lean_dec(v_val_326_);
lean_dec(v_mvar_308_);
v___y_315_ = v_a_309_;
v___y_316_ = v_a_310_;
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
goto v___jp_314_;
}
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; 
lean_dec(v___x_325_);
lean_dec(v_mvar_308_);
v___x_392_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11);
v___x_393_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v___x_392_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
return v___x_393_;
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v_mvar_308_);
v_a_394_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_321_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_321_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
v___jp_314_:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1);
v___x_320_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v___x_319_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___boxed(lean_object* v_right_402_, lean_object* v_mvar_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
uint8_t v_right_boxed_409_; lean_object* v_res_410_; 
v_right_boxed_409_ = lean_unbox(v_right_402_);
v_res_410_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(v_right_boxed_409_, v_mvar_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0(lean_object* v_00_u03b1_411_, lean_object* v_msg_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v_msg_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___boxed(lean_object* v_00_u03b1_419_, lean_object* v_msg_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0(v_00_u03b1_419_, v_msg_420_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2(lean_object* v_mvarId_427_, lean_object* v_val_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(v_mvarId_427_, v_val_428_, v___y_430_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___boxed(lean_object* v_mvarId_435_, lean_object* v_val_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2(v_mvarId_435_, v_val_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3(lean_object* v_00_u03b2_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(v_x_444_, v_x_445_, v_x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_448_, lean_object* v_x_449_, size_t v_x_450_, size_t v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_449_, v_x_450_, v_x_451_, v_x_452_, v_x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_455_, lean_object* v_x_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
size_t v_x_4119__boxed_461_; size_t v_x_4120__boxed_462_; lean_object* v_res_463_; 
v_x_4119__boxed_461_ = lean_unbox_usize(v_x_457_);
lean_dec(v_x_457_);
v_x_4120__boxed_462_ = lean_unbox_usize(v_x_458_);
lean_dec(v_x_458_);
v_res_463_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4(v_00_u03b2_455_, v_x_456_, v_x_4119__boxed_461_, v_x_4120__boxed_462_, v_x_459_, v_x_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_464_, lean_object* v_n_465_, lean_object* v_k_466_, lean_object* v_v_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(v_n_465_, v_k_466_, v_v_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_469_, size_t v_depth_470_, lean_object* v_keys_471_, lean_object* v_vals_472_, lean_object* v_heq_473_, lean_object* v_i_474_, lean_object* v_entries_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_470_, v_keys_471_, v_vals_472_, v_i_474_, v_entries_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_477_, lean_object* v_depth_478_, lean_object* v_keys_479_, lean_object* v_vals_480_, lean_object* v_heq_481_, lean_object* v_i_482_, lean_object* v_entries_483_){
_start:
{
size_t v_depth_boxed_484_; lean_object* v_res_485_; 
v_depth_boxed_484_ = lean_unbox_usize(v_depth_478_);
lean_dec(v_depth_478_);
v_res_485_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_477_, v_depth_boxed_484_, v_keys_479_, v_vals_480_, v_heq_481_, v_i_482_, v_entries_483_);
lean_dec_ref(v_vals_480_);
lean_dec_ref(v_keys_479_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_487_, v_x_488_, v_x_489_, v_x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0(lean_object* v_x_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v___x_502_; 
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_494_);
lean_inc_ref(v___y_493_);
v___x_502_ = lean_apply_9(v_x_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, lean_box(0));
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0___boxed(lean_object* v_x_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0(v_x_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(lean_object* v_mvarId_514_, lean_object* v_x_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___f_525_; lean_object* v___x_526_; 
lean_inc(v___y_519_);
lean_inc_ref(v___y_518_);
lean_inc(v___y_517_);
lean_inc_ref(v___y_516_);
v___f_525_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_525_, 0, v_x_515_);
lean_closure_set(v___f_525_, 1, v___y_516_);
lean_closure_set(v___f_525_, 2, v___y_517_);
lean_closure_set(v___f_525_, 3, v___y_518_);
lean_closure_set(v___f_525_, 4, v___y_519_);
v___x_526_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_514_, v___f_525_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
if (lean_obj_tag(v___x_526_) == 0)
{
return v___x_526_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___boxed(lean_object* v_mvarId_535_, lean_object* v_x_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_mvarId_535_, v_x_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0(lean_object* v_00_u03b1_547_, lean_object* v_mvarId_548_, lean_object* v_x_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_mvarId_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___boxed(lean_object* v_00_u03b1_560_, lean_object* v_mvarId_561_, lean_object* v_x_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0(v_00_u03b1_560_, v_mvarId_561_, v_x_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0(uint8_t v___x_573_, lean_object* v_a_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(v___x_573_, v_a_574_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_584_) == 0)
{
lean_object* v_a_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_a_585_ = lean_ctor_get(v___x_584_, 0);
lean_inc(v_a_585_);
lean_dec_ref_known(v___x_584_, 1);
v___x_586_ = lean_box(0);
v___x_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_587_, 0, v_a_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_587_, v___y_576_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
return v___x_588_;
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_a_589_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_584_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_584_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed(lean_object* v___x_597_, lean_object* v_a_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
uint8_t v___x_1888__boxed_608_; lean_object* v_res_609_; 
v___x_1888__boxed_608_ = lean_unbox(v___x_597_);
v_res_609_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0(v___x_1888__boxed_608_, v_a_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_611_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; uint8_t v___x_621_; lean_object* v___x_622_; lean_object* v___f_623_; lean_object* v___x_624_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc_n(v_a_620_, 2);
lean_dec_ref_known(v___x_619_, 1);
v___x_621_ = 0;
v___x_622_ = lean_box(v___x_621_);
v___f_623_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_623_, 0, v___x_622_);
lean_closure_set(v___f_623_, 1, v_a_620_);
v___x_624_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_a_620_, v___f_623_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_);
return v___x_624_;
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
v_a_625_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_619_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_619_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___boxed(lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft(lean_object* v_x_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___boxed(lean_object* v_x_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft(v_x_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_x_654_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1(){
_start:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_685_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_686_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4));
v___x_687_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8));
v___x_688_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___boxed), 10, 0);
v___x_689_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_685_, v___x_686_, v___x_687_, v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___boxed(lean_object* v_a_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1();
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_693_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___f_705_; lean_object* v___x_706_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc_n(v_a_702_, 2);
lean_dec_ref_known(v___x_701_, 1);
v___x_703_ = 1;
v___x_704_ = lean_box(v___x_703_);
v___f_705_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_705_, 0, v___x_704_);
lean_closure_set(v___f_705_, 1, v_a_702_);
v___x_706_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_a_702_, v___f_705_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
return v___x_706_;
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_707_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_701_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_701_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg___boxed(lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight(lean_object* v_x_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___boxed(lean_object* v_x_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight(v_x_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_x_736_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1(){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_762_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1));
v___x_764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3));
v___x_765_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___boxed), 10, 0);
v___x_766_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_762_, v___x_763_, v___x_764_, v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___boxed(lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lean_Elab_Tactic_Do_ProofMode_LeftRight_0__Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1();
return v_res_768_;
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
