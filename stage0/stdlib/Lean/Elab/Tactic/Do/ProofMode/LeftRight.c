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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
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
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2;
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
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mleft"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(121, 82, 79, 80, 116, 5, 61, 30)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabMLeft"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(121, 20, 10, 20, 51, 143, 96, 253)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mright"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 115, 16, 212, 5, 110, 91, 32)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elabMRight"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(220, 30, 56, 112, 121, 219, 107, 240)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___boxed(lean_object*);
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
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_79_; size_t v___x_80_; size_t v___x_81_; 
v___x_79_ = ((size_t)5ULL);
v___x_80_ = ((size_t)1ULL);
v___x_81_ = lean_usize_shift_left(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; 
v___x_82_ = ((size_t)1ULL);
v___x_83_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_84_ = lean_usize_sub(v___x_83_, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(lean_object* v_x_86_, size_t v_x_87_, size_t v_x_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_object* v_es_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; size_t v___x_95_; lean_object* v_j_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_es_91_ = lean_ctor_get(v_x_86_, 0);
v___x_92_ = ((size_t)5ULL);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_95_ = lean_usize_land(v_x_87_, v___x_94_);
v_j_96_ = lean_usize_to_nat(v___x_95_);
v___x_97_ = lean_array_get_size(v_es_91_);
v___x_98_ = lean_nat_dec_lt(v_j_96_, v___x_97_);
if (v___x_98_ == 0)
{
lean_dec(v_j_96_);
lean_dec(v_x_90_);
lean_dec(v_x_89_);
return v_x_86_;
}
else
{
lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_135_; 
lean_inc_ref(v_es_91_);
v_isSharedCheck_135_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; 
v_unused_136_ = lean_ctor_get(v_x_86_, 0);
lean_dec(v_unused_136_);
v___x_100_ = v_x_86_;
v_isShared_101_ = v_isSharedCheck_135_;
goto v_resetjp_99_;
}
else
{
lean_dec(v_x_86_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_135_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v_v_102_; lean_object* v___x_103_; lean_object* v_xs_x27_104_; lean_object* v___y_106_; 
v_v_102_ = lean_array_fget(v_es_91_, v_j_96_);
v___x_103_ = lean_box(0);
v_xs_x27_104_ = lean_array_fset(v_es_91_, v_j_96_, v___x_103_);
switch(lean_obj_tag(v_v_102_))
{
case 0:
{
lean_object* v_key_111_; lean_object* v_val_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_122_; 
v_key_111_ = lean_ctor_get(v_v_102_, 0);
v_val_112_ = lean_ctor_get(v_v_102_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_v_102_);
if (v_isSharedCheck_122_ == 0)
{
v___x_114_ = v_v_102_;
v_isShared_115_ = v_isSharedCheck_122_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_val_112_);
lean_inc(v_key_111_);
lean_dec(v_v_102_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_122_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
uint8_t v___x_116_; 
v___x_116_ = l_Lean_instBEqMVarId_beq(v_x_89_, v_key_111_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_del_object(v___x_114_);
v___x_117_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_111_, v_val_112_, v_x_89_, v_x_90_);
v___x_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
v___y_106_ = v___x_118_;
goto v___jp_105_;
}
else
{
lean_object* v___x_120_; 
lean_dec(v_val_112_);
lean_dec(v_key_111_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v_x_90_);
lean_ctor_set(v___x_114_, 0, v_x_89_);
v___x_120_ = v___x_114_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_x_89_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_x_90_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
v___y_106_ = v___x_120_;
goto v___jp_105_;
}
}
}
}
case 1:
{
lean_object* v_node_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_133_; 
v_node_123_ = lean_ctor_get(v_v_102_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v_v_102_);
if (v_isSharedCheck_133_ == 0)
{
v___x_125_ = v_v_102_;
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_node_123_);
lean_dec(v_v_102_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_127_ = lean_usize_shift_right(v_x_87_, v___x_92_);
v___x_128_ = lean_usize_add(v_x_88_, v___x_93_);
v___x_129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_node_123_, v___x_127_, v___x_128_, v_x_89_, v_x_90_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_129_);
v___x_131_ = v___x_125_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
v___y_106_ = v___x_131_;
goto v___jp_105_;
}
}
}
default: 
{
lean_object* v___x_134_; 
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_x_89_);
lean_ctor_set(v___x_134_, 1, v_x_90_);
v___y_106_ = v___x_134_;
goto v___jp_105_;
}
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_107_ = lean_array_fset(v_xs_x27_104_, v_j_96_, v___y_106_);
lean_dec(v_j_96_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_107_);
v___x_109_ = v___x_100_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
else
{
lean_object* v_ks_137_; lean_object* v_vs_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_158_; 
v_ks_137_ = lean_ctor_get(v_x_86_, 0);
v_vs_138_ = lean_ctor_get(v_x_86_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_158_ == 0)
{
v___x_140_ = v_x_86_;
v_isShared_141_ = v_isSharedCheck_158_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_vs_138_);
lean_inc(v_ks_137_);
lean_dec(v_x_86_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_158_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_ks_137_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_vs_138_);
v___x_143_ = v_reuseFailAlloc_157_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v_newNode_144_; uint8_t v___y_146_; size_t v___x_152_; uint8_t v___x_153_; 
v_newNode_144_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(v___x_143_, v_x_89_, v_x_90_);
v___x_152_ = ((size_t)7ULL);
v___x_153_ = lean_usize_dec_le(v___x_152_, v_x_88_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_144_);
v___x_155_ = lean_unsigned_to_nat(4u);
v___x_156_ = lean_nat_dec_lt(v___x_154_, v___x_155_);
lean_dec(v___x_154_);
v___y_146_ = v___x_156_;
goto v___jp_145_;
}
else
{
v___y_146_ = v___x_153_;
goto v___jp_145_;
}
v___jp_145_:
{
if (v___y_146_ == 0)
{
lean_object* v_ks_147_; lean_object* v_vs_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_ks_147_ = lean_ctor_get(v_newNode_144_, 0);
lean_inc_ref(v_ks_147_);
v_vs_148_ = lean_ctor_get(v_newNode_144_, 1);
lean_inc_ref(v_vs_148_);
lean_dec_ref(v_newNode_144_);
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_x_88_, v_ks_147_, v_vs_148_, v___x_149_, v___x_150_);
lean_dec_ref(v_vs_148_);
lean_dec_ref(v_ks_147_);
return v___x_151_;
}
else
{
return v_newNode_144_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(size_t v_depth_159_, lean_object* v_keys_160_, lean_object* v_vals_161_, lean_object* v_i_162_, lean_object* v_entries_163_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_array_get_size(v_keys_160_);
v___x_165_ = lean_nat_dec_lt(v_i_162_, v___x_164_);
if (v___x_165_ == 0)
{
lean_dec(v_i_162_);
return v_entries_163_;
}
else
{
lean_object* v_k_166_; lean_object* v_v_167_; uint64_t v___x_168_; size_t v_h_169_; size_t v___x_170_; lean_object* v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v_h_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_k_166_ = lean_array_fget_borrowed(v_keys_160_, v_i_162_);
v_v_167_ = lean_array_fget_borrowed(v_vals_161_, v_i_162_);
v___x_168_ = l_Lean_instHashableMVarId_hash(v_k_166_);
v_h_169_ = lean_uint64_to_usize(v___x_168_);
v___x_170_ = ((size_t)5ULL);
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_sub(v_depth_159_, v___x_172_);
v___x_174_ = lean_usize_mul(v___x_170_, v___x_173_);
v_h_175_ = lean_usize_shift_right(v_h_169_, v___x_174_);
v___x_176_ = lean_nat_add(v_i_162_, v___x_171_);
lean_dec(v_i_162_);
lean_inc(v_v_167_);
lean_inc(v_k_166_);
v___x_177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_entries_163_, v_h_175_, v_depth_159_, v_k_166_, v_v_167_);
v_i_162_ = v___x_176_;
v_entries_163_ = v___x_177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_depth_179_, lean_object* v_keys_180_, lean_object* v_vals_181_, lean_object* v_i_182_, lean_object* v_entries_183_){
_start:
{
size_t v_depth_boxed_184_; lean_object* v_res_185_; 
v_depth_boxed_184_ = lean_unbox_usize(v_depth_179_);
lean_dec(v_depth_179_);
v_res_185_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_184_, v_keys_180_, v_vals_181_, v_i_182_, v_entries_183_);
lean_dec_ref(v_vals_181_);
lean_dec_ref(v_keys_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
size_t v_x_3568__boxed_191_; size_t v_x_3569__boxed_192_; lean_object* v_res_193_; 
v_x_3568__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_x_3569__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_res_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_186_, v_x_3568__boxed_191_, v_x_3569__boxed_192_, v_x_189_, v_x_190_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
uint64_t v___x_197_; size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v___x_197_ = l_Lean_instHashableMVarId_hash(v_x_195_);
v___x_198_ = lean_uint64_to_usize(v___x_197_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_194_, v___x_198_, v___x_199_, v_x_195_, v_x_196_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(lean_object* v_mvarId_201_, lean_object* v_val_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; lean_object* v_mctx_206_; lean_object* v_cache_207_; lean_object* v_zetaDeltaFVarIds_208_; lean_object* v_postponed_209_; lean_object* v_diag_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_237_; 
v___x_205_ = lean_st_ref_take(v___y_203_);
v_mctx_206_ = lean_ctor_get(v___x_205_, 0);
v_cache_207_ = lean_ctor_get(v___x_205_, 1);
v_zetaDeltaFVarIds_208_ = lean_ctor_get(v___x_205_, 2);
v_postponed_209_ = lean_ctor_get(v___x_205_, 3);
v_diag_210_ = lean_ctor_get(v___x_205_, 4);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_237_ == 0)
{
v___x_212_ = v___x_205_;
v_isShared_213_ = v_isSharedCheck_237_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_diag_210_);
lean_inc(v_postponed_209_);
lean_inc(v_zetaDeltaFVarIds_208_);
lean_inc(v_cache_207_);
lean_inc(v_mctx_206_);
lean_dec(v___x_205_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_237_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_depth_214_; lean_object* v_levelAssignDepth_215_; lean_object* v_mvarCounter_216_; lean_object* v_lDepth_217_; lean_object* v_decls_218_; lean_object* v_userNames_219_; lean_object* v_lAssignment_220_; lean_object* v_eAssignment_221_; lean_object* v_dAssignment_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_236_; 
v_depth_214_ = lean_ctor_get(v_mctx_206_, 0);
v_levelAssignDepth_215_ = lean_ctor_get(v_mctx_206_, 1);
v_mvarCounter_216_ = lean_ctor_get(v_mctx_206_, 2);
v_lDepth_217_ = lean_ctor_get(v_mctx_206_, 3);
v_decls_218_ = lean_ctor_get(v_mctx_206_, 4);
v_userNames_219_ = lean_ctor_get(v_mctx_206_, 5);
v_lAssignment_220_ = lean_ctor_get(v_mctx_206_, 6);
v_eAssignment_221_ = lean_ctor_get(v_mctx_206_, 7);
v_dAssignment_222_ = lean_ctor_get(v_mctx_206_, 8);
v_isSharedCheck_236_ = !lean_is_exclusive(v_mctx_206_);
if (v_isSharedCheck_236_ == 0)
{
v___x_224_ = v_mctx_206_;
v_isShared_225_ = v_isSharedCheck_236_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_dAssignment_222_);
lean_inc(v_eAssignment_221_);
lean_inc(v_lAssignment_220_);
lean_inc(v_userNames_219_);
lean_inc(v_decls_218_);
lean_inc(v_lDepth_217_);
lean_inc(v_mvarCounter_216_);
lean_inc(v_levelAssignDepth_215_);
lean_inc(v_depth_214_);
lean_dec(v_mctx_206_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_236_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_226_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(v_eAssignment_221_, v_mvarId_201_, v_val_202_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 7, v___x_226_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v_depth_214_);
lean_ctor_set(v_reuseFailAlloc_235_, 1, v_levelAssignDepth_215_);
lean_ctor_set(v_reuseFailAlloc_235_, 2, v_mvarCounter_216_);
lean_ctor_set(v_reuseFailAlloc_235_, 3, v_lDepth_217_);
lean_ctor_set(v_reuseFailAlloc_235_, 4, v_decls_218_);
lean_ctor_set(v_reuseFailAlloc_235_, 5, v_userNames_219_);
lean_ctor_set(v_reuseFailAlloc_235_, 6, v_lAssignment_220_);
lean_ctor_set(v_reuseFailAlloc_235_, 7, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_235_, 8, v_dAssignment_222_);
v___x_228_ = v_reuseFailAlloc_235_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_230_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_228_);
v___x_230_ = v___x_212_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_cache_207_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_zetaDeltaFVarIds_208_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_postponed_209_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v_diag_210_);
v___x_230_ = v_reuseFailAlloc_234_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_st_ref_set(v___y_203_, v___x_230_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(lean_object* v_msgData_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; lean_object* v_env_250_; lean_object* v___x_251_; lean_object* v_mctx_252_; lean_object* v_lctx_253_; lean_object* v_options_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_249_ = lean_st_ref_get(v___y_247_);
v_env_250_ = lean_ctor_get(v___x_249_, 0);
lean_inc_ref(v_env_250_);
lean_dec(v___x_249_);
v___x_251_ = lean_st_ref_get(v___y_245_);
v_mctx_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc_ref(v_mctx_252_);
lean_dec(v___x_251_);
v_lctx_253_ = lean_ctor_get(v___y_244_, 2);
v_options_254_ = lean_ctor_get(v___y_246_, 2);
lean_inc_ref(v_options_254_);
lean_inc_ref(v_lctx_253_);
v___x_255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_255_, 0, v_env_250_);
lean_ctor_set(v___x_255_, 1, v_mctx_252_);
lean_ctor_set(v___x_255_, 2, v_lctx_253_);
lean_ctor_set(v___x_255_, 3, v_options_254_);
v___x_256_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_msgData_243_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0___boxed(lean_object* v_msgData_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(v_msgData_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_ref_271_; lean_object* v___x_272_; lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_281_; 
v_ref_271_ = lean_ctor_get(v___y_268_, 5);
v___x_272_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0_spec__0(v_msg_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
v_a_273_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_281_ == 0)
{
v___x_275_ = v___x_272_;
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_281_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_279_; 
lean_inc(v_ref_271_);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v_ref_271_);
lean_ctor_set(v___x_277_, 1, v_a_273_);
if (v_isShared_276_ == 0)
{
lean_ctor_set_tag(v___x_275_, 1);
lean_ctor_set(v___x_275_, 0, v___x_277_);
v___x_279_ = v___x_275_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg___boxed(lean_object* v_msg_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v_msg_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_288_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__0));
v___x_291_ = l_Lean_stringToMessageData(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__10));
v___x_310_ = l_Lean_stringToMessageData(v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(uint8_t v_right_311_, lean_object* v_mvar_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___x_325_; 
lean_inc(v_mvar_312_);
v___x_325_ = l_Lean_MVarId_getType(v_mvar_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; lean_object* v_a_328_; lean_object* v___x_329_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref(v___x_325_);
v___x_327_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__1___redArg(v_a_326_, v_a_314_);
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref(v___x_327_);
v___x_329_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_328_);
lean_dec(v_a_328_);
if (lean_obj_tag(v___x_329_) == 1)
{
lean_object* v_val_330_; lean_object* v_target_331_; 
v_val_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_val_330_);
lean_dec_ref(v___x_329_);
v_target_331_ = lean_ctor_get(v_val_330_, 3);
lean_inc_ref(v_target_331_);
if (lean_obj_tag(v_target_331_) == 5)
{
lean_object* v_fn_332_; 
v_fn_332_ = lean_ctor_get(v_target_331_, 0);
lean_inc_ref(v_fn_332_);
if (lean_obj_tag(v_fn_332_) == 5)
{
lean_object* v_fn_333_; 
v_fn_333_ = lean_ctor_get(v_fn_332_, 0);
lean_inc_ref(v_fn_333_);
if (lean_obj_tag(v_fn_333_) == 5)
{
lean_object* v_fn_334_; 
v_fn_334_ = lean_ctor_get(v_fn_333_, 0);
if (lean_obj_tag(v_fn_334_) == 4)
{
lean_object* v_declName_335_; 
v_declName_335_ = lean_ctor_get(v_fn_334_, 0);
lean_inc(v_declName_335_);
if (lean_obj_tag(v_declName_335_) == 1)
{
lean_object* v_pre_336_; 
v_pre_336_ = lean_ctor_get(v_declName_335_, 0);
lean_inc(v_pre_336_);
if (lean_obj_tag(v_pre_336_) == 1)
{
lean_object* v_pre_337_; 
v_pre_337_ = lean_ctor_get(v_pre_336_, 0);
lean_inc(v_pre_337_);
if (lean_obj_tag(v_pre_337_) == 1)
{
lean_object* v_pre_338_; 
v_pre_338_ = lean_ctor_get(v_pre_337_, 0);
lean_inc(v_pre_338_);
if (lean_obj_tag(v_pre_338_) == 1)
{
lean_object* v_u_339_; lean_object* v_00_u03c3s_340_; lean_object* v_hyps_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_394_; 
v_u_339_ = lean_ctor_get(v_val_330_, 0);
v_00_u03c3s_340_ = lean_ctor_get(v_val_330_, 1);
v_hyps_341_ = lean_ctor_get(v_val_330_, 2);
v_isSharedCheck_394_ = !lean_is_exclusive(v_val_330_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; 
v_unused_395_ = lean_ctor_get(v_val_330_, 3);
lean_dec(v_unused_395_);
v___x_343_ = v_val_330_;
v_isShared_344_ = v_isSharedCheck_394_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_hyps_341_);
lean_inc(v_00_u03c3s_340_);
lean_inc(v_u_339_);
lean_dec(v_val_330_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_394_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v_arg_345_; lean_object* v_arg_346_; lean_object* v_arg_347_; lean_object* v_str_348_; lean_object* v_str_349_; lean_object* v_str_350_; lean_object* v_pre_351_; lean_object* v_str_352_; lean_object* v_fst_354_; lean_object* v_snd_355_; 
v_arg_345_ = lean_ctor_get(v_target_331_, 1);
lean_inc_ref(v_arg_345_);
lean_dec_ref(v_target_331_);
v_arg_346_ = lean_ctor_get(v_fn_332_, 1);
lean_inc_ref(v_arg_346_);
lean_dec_ref(v_fn_332_);
v_arg_347_ = lean_ctor_get(v_fn_333_, 1);
lean_inc_ref(v_arg_347_);
lean_dec_ref(v_fn_333_);
v_str_348_ = lean_ctor_get(v_declName_335_, 1);
lean_inc_ref(v_str_348_);
lean_dec_ref(v_declName_335_);
v_str_349_ = lean_ctor_get(v_pre_336_, 1);
lean_inc_ref(v_str_349_);
lean_dec_ref(v_pre_336_);
v_str_350_ = lean_ctor_get(v_pre_337_, 1);
lean_inc_ref(v_str_350_);
lean_dec_ref(v_pre_337_);
v_pre_351_ = lean_ctor_get(v_pre_338_, 0);
lean_inc(v_pre_351_);
v_str_352_ = lean_ctor_get(v_pre_338_, 1);
lean_inc_ref(v_str_352_);
lean_dec_ref(v_pre_338_);
if (lean_obj_tag(v_pre_351_) == 0)
{
lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__2));
v___x_385_ = lean_string_dec_eq(v_str_352_, v___x_384_);
lean_dec_ref(v_str_352_);
if (v___x_385_ == 0)
{
lean_dec_ref(v_str_350_);
lean_dec_ref(v_str_349_);
lean_dec_ref(v_str_348_);
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_del_object(v___x_343_);
lean_dec_ref(v_hyps_341_);
lean_dec_ref(v_00_u03c3s_340_);
lean_dec(v_u_339_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
else
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__3));
v___x_387_ = lean_string_dec_eq(v_str_350_, v___x_386_);
lean_dec_ref(v_str_350_);
if (v___x_387_ == 0)
{
lean_dec_ref(v_str_349_);
lean_dec_ref(v_str_348_);
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_del_object(v___x_343_);
lean_dec_ref(v_hyps_341_);
lean_dec_ref(v_00_u03c3s_340_);
lean_dec(v_u_339_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
else
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__4));
v___x_389_ = lean_string_dec_eq(v_str_349_, v___x_388_);
lean_dec_ref(v_str_349_);
if (v___x_389_ == 0)
{
lean_dec_ref(v_str_348_);
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_del_object(v___x_343_);
lean_dec_ref(v_hyps_341_);
lean_dec_ref(v_00_u03c3s_340_);
lean_dec(v_u_339_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
else
{
lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__5));
v___x_391_ = lean_string_dec_eq(v_str_348_, v___x_390_);
lean_dec_ref(v_str_348_);
if (v___x_391_ == 0)
{
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_del_object(v___x_343_);
lean_dec_ref(v_hyps_341_);
lean_dec_ref(v_00_u03c3s_340_);
lean_dec(v_u_339_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
else
{
if (v_right_311_ == 0)
{
lean_object* v___x_392_; 
v___x_392_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__7));
lean_inc_ref(v_arg_346_);
v_fst_354_ = v___x_392_;
v_snd_355_ = v_arg_346_;
goto v___jp_353_;
}
else
{
lean_object* v___x_393_; 
v___x_393_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__9));
lean_inc_ref(v_arg_345_);
v_fst_354_ = v___x_393_;
v_snd_355_ = v_arg_345_;
goto v___jp_353_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_str_352_);
lean_dec(v_pre_351_);
lean_dec_ref(v_str_350_);
lean_dec_ref(v_str_349_);
lean_dec_ref(v_str_348_);
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_del_object(v___x_343_);
lean_dec_ref(v_hyps_341_);
lean_dec_ref(v_00_u03c3s_340_);
lean_dec(v_u_339_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
v___jp_353_:
{
lean_object* v___x_357_; 
lean_inc_ref(v_hyps_341_);
lean_inc(v_u_339_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 3, v_snd_355_);
v___x_357_ = v___x_343_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_u_339_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_00_u03c3s_340_);
lean_ctor_set(v_reuseFailAlloc_383_, 2, v_hyps_341_);
lean_ctor_set(v_reuseFailAlloc_383_, 3, v_snd_355_);
v___x_357_ = v_reuseFailAlloc_383_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_357_);
v___x_359_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_358_, v_pre_351_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref(v___x_359_);
v___x_361_ = lean_box(0);
v___x_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_362_, 0, v_u_339_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = l_Lean_mkConst(v_fst_354_, v___x_362_);
lean_inc(v_a_360_);
v___x_364_ = l_Lean_mkApp5(v___x_363_, v_arg_347_, v_hyps_341_, v_arg_346_, v_arg_345_, v_a_360_);
v___x_365_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(v_mvar_312_, v___x_364_, v_a_314_);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_373_ == 0)
{
lean_object* v_unused_374_; 
v_unused_374_ = lean_ctor_get(v___x_365_, 0);
lean_dec(v_unused_374_);
v___x_367_ = v___x_365_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_dec(v___x_365_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = l_Lean_Expr_mvarId_x21(v_a_360_);
lean_dec(v_a_360_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
lean_dec(v_fst_354_);
lean_dec_ref(v_arg_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_dec_ref(v_hyps_341_);
lean_dec(v_u_339_);
lean_dec(v_mvar_312_);
v_a_375_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_359_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_359_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_337_);
lean_dec(v_pre_338_);
lean_dec_ref(v_pre_336_);
lean_dec_ref(v_declName_335_);
lean_dec_ref(v_fn_333_);
lean_dec_ref(v_fn_332_);
lean_dec_ref(v_target_331_);
lean_dec(v_val_330_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
}
else
{
lean_dec_ref(v_pre_336_);
lean_dec(v_pre_337_);
lean_dec_ref(v_declName_335_);
lean_dec_ref(v_fn_333_);
lean_dec_ref(v_fn_332_);
lean_dec_ref(v_target_331_);
lean_dec(v_val_330_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
}
else
{
lean_dec(v_pre_336_);
lean_dec_ref(v_declName_335_);
lean_dec_ref(v_fn_333_);
lean_dec_ref(v_fn_332_);
lean_dec_ref(v_target_331_);
lean_dec(v_val_330_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
}
else
{
lean_dec(v_declName_335_);
lean_dec_ref(v_fn_333_);
lean_dec_ref(v_fn_332_);
lean_dec_ref(v_target_331_);
lean_dec(v_val_330_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
}
else
{
lean_dec_ref(v_fn_333_);
lean_dec_ref(v_fn_332_);
lean_dec_ref(v_target_331_);
lean_dec(v_val_330_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
}
else
{
lean_dec_ref(v_fn_332_);
lean_dec_ref(v_fn_333_);
lean_dec_ref(v_target_331_);
lean_dec(v_val_330_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
}
else
{
lean_dec_ref(v_target_331_);
lean_dec_ref(v_fn_332_);
lean_dec(v_val_330_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
}
else
{
lean_dec_ref(v_target_331_);
lean_dec(v_val_330_);
lean_dec(v_mvar_312_);
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
v___y_321_ = v_a_315_;
v___y_322_ = v_a_316_;
goto v___jp_318_;
}
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec(v___x_329_);
lean_dec(v_mvar_312_);
v___x_396_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11, &l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__11);
v___x_397_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v___x_396_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
return v___x_397_;
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec(v_mvar_312_);
v_a_398_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_325_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_325_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
v___jp_318_:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___closed__1);
v___x_324_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v___x_323_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore___boxed(lean_object* v_right_406_, lean_object* v_mvar_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
uint8_t v_right_boxed_413_; lean_object* v_res_414_; 
v_right_boxed_413_ = lean_unbox(v_right_406_);
v_res_414_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(v_right_boxed_413_, v_mvar_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0(lean_object* v_00_u03b1_415_, lean_object* v_msg_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___redArg(v_msg_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0___boxed(lean_object* v_00_u03b1_423_, lean_object* v_msg_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__0(v_00_u03b1_423_, v_msg_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2(lean_object* v_mvarId_431_, lean_object* v_val_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___redArg(v_mvarId_431_, v_val_432_, v___y_434_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2___boxed(lean_object* v_mvarId_439_, lean_object* v_val_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2(v_mvarId_439_, v_val_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3(lean_object* v_00_u03b2_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3___redArg(v_x_448_, v_x_449_, v_x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_452_, lean_object* v_x_453_, size_t v_x_454_, size_t v_x_455_, lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___redArg(v_x_453_, v_x_454_, v_x_455_, v_x_456_, v_x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_459_, lean_object* v_x_460_, lean_object* v_x_461_, lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
size_t v_x_4131__boxed_465_; size_t v_x_4132__boxed_466_; lean_object* v_res_467_; 
v_x_4131__boxed_465_ = lean_unbox_usize(v_x_461_);
lean_dec(v_x_461_);
v_x_4132__boxed_466_ = lean_unbox_usize(v_x_462_);
lean_dec(v_x_462_);
v_res_467_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4(v_00_u03b2_459_, v_x_460_, v_x_4131__boxed_465_, v_x_4132__boxed_466_, v_x_463_, v_x_464_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_468_, lean_object* v_n_469_, lean_object* v_k_470_, lean_object* v_v_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5___redArg(v_n_469_, v_k_470_, v_v_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_473_, size_t v_depth_474_, lean_object* v_keys_475_, lean_object* v_vals_476_, lean_object* v_heq_477_, lean_object* v_i_478_, lean_object* v_entries_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_474_, v_keys_475_, v_vals_476_, v_i_478_, v_entries_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_481_, lean_object* v_depth_482_, lean_object* v_keys_483_, lean_object* v_vals_484_, lean_object* v_heq_485_, lean_object* v_i_486_, lean_object* v_entries_487_){
_start:
{
size_t v_depth_boxed_488_; lean_object* v_res_489_; 
v_depth_boxed_488_ = lean_unbox_usize(v_depth_482_);
lean_dec(v_depth_482_);
v_res_489_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_481_, v_depth_boxed_488_, v_keys_483_, v_vals_484_, v_heq_485_, v_i_486_, v_entries_487_);
lean_dec_ref(v_vals_484_);
lean_dec_ref(v_keys_483_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_490_, lean_object* v_x_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_491_, v_x_492_, v_x_493_, v_x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0(lean_object* v_x_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; 
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
v___x_506_ = lean_apply_9(v_x_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, lean_box(0));
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0___boxed(lean_object* v_x_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0(v_x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(lean_object* v_mvarId_518_, lean_object* v_x_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___f_529_; lean_object* v___x_530_; 
lean_inc(v___y_523_);
lean_inc_ref(v___y_522_);
lean_inc(v___y_521_);
lean_inc_ref(v___y_520_);
v___f_529_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_529_, 0, v_x_519_);
lean_closure_set(v___f_529_, 1, v___y_520_);
lean_closure_set(v___f_529_, 2, v___y_521_);
lean_closure_set(v___f_529_, 3, v___y_522_);
lean_closure_set(v___f_529_, 4, v___y_523_);
v___x_530_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_518_, v___f_529_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_530_) == 0)
{
return v___x_530_;
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg___boxed(lean_object* v_mvarId_539_, lean_object* v_x_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_mvarId_539_, v_x_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0(lean_object* v_00_u03b1_551_, lean_object* v_mvarId_552_, lean_object* v_x_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_mvarId_552_, v_x_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___boxed(lean_object* v_00_u03b1_564_, lean_object* v_mvarId_565_, lean_object* v_x_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0(v_00_u03b1_564_, v_mvarId_565_, v_x_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0(uint8_t v___x_577_, lean_object* v_a_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Elab_Tactic_Do_ProofMode_mLeftRightCore(v___x_577_, v_a_578_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref(v___x_588_);
v___x_590_ = lean_box(0);
v___x_591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_591_, 0, v_a_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_591_, v___y_580_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
return v___x_592_;
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
v_a_593_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_588_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_588_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed(lean_object* v___x_601_, lean_object* v_a_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
uint8_t v___x_1888__boxed_612_; lean_object* v_res_613_; 
v___x_1888__boxed_612_ = lean_unbox(v___x_601_);
v_res_613_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0(v___x_1888__boxed_612_, v_a_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_615_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___f_627_; lean_object* v___x_628_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref(v___x_623_);
v___x_625_ = 0;
v___x_626_ = lean_box(v___x_625_);
lean_inc(v_a_624_);
v___f_627_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_627_, 0, v___x_626_);
lean_closure_set(v___f_627_, 1, v_a_624_);
v___x_628_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_a_624_, v___f_627_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_);
return v___x_628_;
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
v_a_629_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_623_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_623_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___boxed(lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_, v_a_644_);
lean_dec(v_a_644_);
lean_dec_ref(v_a_643_);
lean_dec(v_a_642_);
lean_dec_ref(v_a_641_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft(lean_object* v_x_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg(v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___boxed(lean_object* v_x_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft(v_x_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_);
lean_dec(v_a_666_);
lean_dec_ref(v_a_665_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_x_658_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1(){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_689_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_690_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__4));
v___x_691_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___closed__8));
v___x_692_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___boxed), 10, 0);
v___x_693_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_689_, v___x_690_, v___x_691_, v___x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1___boxed(lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1();
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_697_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; uint8_t v___x_707_; lean_object* v___x_708_; lean_object* v___f_709_; lean_object* v___x_710_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref(v___x_705_);
v___x_707_ = 1;
v___x_708_ = lean_box(v___x_707_);
lean_inc(v_a_706_);
v___f_709_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_709_, 0, v___x_708_);
lean_closure_set(v___f_709_, 1, v_a_706_);
v___x_710_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMLeft_spec__0___redArg(v_a_706_, v___f_709_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_);
return v___x_710_;
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
v_a_711_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_705_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_705_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg___boxed(lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight(lean_object* v_x_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___redArg(v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_, v_a_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___boxed(lean_object* v_x_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight(v_x_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_x_740_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1(){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_766_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_767_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__1));
v___x_768_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___closed__3));
v___x_769_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___boxed), 10, 0);
v___x_770_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_766_, v___x_767_, v___x_768_, v___x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1___boxed(lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1();
return v_res_772_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_LeftRight(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMLeft___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMLeft__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMRight___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMRight__1();
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
