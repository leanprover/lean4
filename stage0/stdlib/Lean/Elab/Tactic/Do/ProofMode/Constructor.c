// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Constructor
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "target is not SPred.and"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "and_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 10, 80, 59, 91, 116, 13, 118)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not in proof mode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mconstructor"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(115, 154, 195, 216, 142, 75, 110, 212)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elabMConstructor"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(14, 68, 128, 8, 115, 239, 72, 179)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_e_30_, v___y_32_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1(v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(lean_object* v_msgData_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_50_; lean_object* v_env_51_; lean_object* v___x_52_; lean_object* v_mctx_53_; lean_object* v_lctx_54_; lean_object* v_options_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_50_ = lean_st_ref_get(v___y_48_);
v_env_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc_ref(v_env_51_);
lean_dec(v___x_50_);
v___x_52_ = lean_st_ref_get(v___y_46_);
v_mctx_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc_ref(v_mctx_53_);
lean_dec(v___x_52_);
v_lctx_54_ = lean_ctor_get(v___y_45_, 2);
v_options_55_ = lean_ctor_get(v___y_47_, 2);
lean_inc_ref(v_options_55_);
lean_inc_ref(v_lctx_54_);
v___x_56_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_56_, 0, v_env_51_);
lean_ctor_set(v___x_56_, 1, v_mctx_53_);
lean_ctor_set(v___x_56_, 2, v_lctx_54_);
lean_ctor_set(v___x_56_, 3, v_options_55_);
v___x_57_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v_msgData_44_);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0___boxed(lean_object* v_msgData_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(v_msgData_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(lean_object* v_msg_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_ref_72_; lean_object* v___x_73_; lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_82_; 
v_ref_72_ = lean_ctor_get(v___y_69_, 5);
v___x_73_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(v_msg_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_82_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
lean_inc(v_ref_72_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v_ref_72_);
lean_ctor_set(v___x_78_, 1, v_a_74_);
if (v_isShared_77_ == 0)
{
lean_ctor_set_tag(v___x_76_, 1);
lean_ctor_set(v___x_76_, 0, v___x_78_);
v___x_80_ = v___x_76_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg___boxed(lean_object* v_msg_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v_msg_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_x_90_, lean_object* v_x_91_, lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
lean_object* v_ks_94_; lean_object* v_vs_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_119_; 
v_ks_94_ = lean_ctor_get(v_x_90_, 0);
v_vs_95_ = lean_ctor_get(v_x_90_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v_x_90_);
if (v_isSharedCheck_119_ == 0)
{
v___x_97_ = v_x_90_;
v_isShared_98_ = v_isSharedCheck_119_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_vs_95_);
lean_inc(v_ks_94_);
lean_dec(v_x_90_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_119_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_array_get_size(v_ks_94_);
v___x_100_ = lean_nat_dec_lt(v_x_91_, v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
lean_dec(v_x_91_);
v___x_101_ = lean_array_push(v_ks_94_, v_x_92_);
v___x_102_ = lean_array_push(v_vs_95_, v_x_93_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v___x_102_);
lean_ctor_set(v___x_97_, 0, v___x_101_);
v___x_104_ = v___x_97_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
else
{
lean_object* v_k_x27_106_; uint8_t v___x_107_; 
v_k_x27_106_ = lean_array_fget_borrowed(v_ks_94_, v_x_91_);
v___x_107_ = l_Lean_instBEqMVarId_beq(v_x_92_, v_k_x27_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_109_; 
if (v_isShared_98_ == 0)
{
v___x_109_ = v___x_97_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_ks_94_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_vs_95_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_add(v_x_91_, v___x_110_);
lean_dec(v_x_91_);
v_x_90_ = v___x_109_;
v_x_91_ = v___x_111_;
goto _start;
}
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_114_ = lean_array_fset(v_ks_94_, v_x_91_, v_x_92_);
v___x_115_ = lean_array_fset(v_vs_95_, v_x_91_, v_x_93_);
lean_dec(v_x_91_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v___x_115_);
lean_ctor_set(v___x_97_, 0, v___x_114_);
v___x_117_ = v___x_97_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_n_120_, lean_object* v_k_121_, lean_object* v_v_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_120_, v___x_123_, v_k_121_, v_v_122_);
return v___x_124_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_125_; size_t v___x_126_; size_t v___x_127_; 
v___x_125_ = ((size_t)5ULL);
v___x_126_ = ((size_t)1ULL);
v___x_127_ = lean_usize_shift_left(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; 
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_130_ = lean_usize_sub(v___x_129_, v___x_128_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(lean_object* v_x_132_, size_t v_x_133_, size_t v_x_134_, lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v_es_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v___x_141_; lean_object* v_j_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_es_137_ = lean_ctor_get(v_x_132_, 0);
v___x_138_ = ((size_t)5ULL);
v___x_139_ = ((size_t)1ULL);
v___x_140_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_141_ = lean_usize_land(v_x_133_, v___x_140_);
v_j_142_ = lean_usize_to_nat(v___x_141_);
v___x_143_ = lean_array_get_size(v_es_137_);
v___x_144_ = lean_nat_dec_lt(v_j_142_, v___x_143_);
if (v___x_144_ == 0)
{
lean_dec(v_j_142_);
lean_dec(v_x_136_);
lean_dec(v_x_135_);
return v_x_132_;
}
else
{
lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_181_; 
lean_inc_ref(v_es_137_);
v_isSharedCheck_181_ = !lean_is_exclusive(v_x_132_);
if (v_isSharedCheck_181_ == 0)
{
lean_object* v_unused_182_; 
v_unused_182_ = lean_ctor_get(v_x_132_, 0);
lean_dec(v_unused_182_);
v___x_146_ = v_x_132_;
v_isShared_147_ = v_isSharedCheck_181_;
goto v_resetjp_145_;
}
else
{
lean_dec(v_x_132_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_181_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_v_148_; lean_object* v___x_149_; lean_object* v_xs_x27_150_; lean_object* v___y_152_; 
v_v_148_ = lean_array_fget(v_es_137_, v_j_142_);
v___x_149_ = lean_box(0);
v_xs_x27_150_ = lean_array_fset(v_es_137_, v_j_142_, v___x_149_);
switch(lean_obj_tag(v_v_148_))
{
case 0:
{
lean_object* v_key_157_; lean_object* v_val_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_168_; 
v_key_157_ = lean_ctor_get(v_v_148_, 0);
v_val_158_ = lean_ctor_get(v_v_148_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_v_148_);
if (v_isSharedCheck_168_ == 0)
{
v___x_160_ = v_v_148_;
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_val_158_);
lean_inc(v_key_157_);
lean_dec(v_v_148_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_168_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
uint8_t v___x_162_; 
v___x_162_ = l_Lean_instBEqMVarId_beq(v_x_135_, v_key_157_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_del_object(v___x_160_);
v___x_163_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_157_, v_val_158_, v_x_135_, v_x_136_);
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
v___y_152_ = v___x_164_;
goto v___jp_151_;
}
else
{
lean_object* v___x_166_; 
lean_dec(v_val_158_);
lean_dec(v_key_157_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v_x_136_);
lean_ctor_set(v___x_160_, 0, v_x_135_);
v___x_166_ = v___x_160_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_x_135_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_x_136_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
v___y_152_ = v___x_166_;
goto v___jp_151_;
}
}
}
}
case 1:
{
lean_object* v_node_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_179_; 
v_node_169_ = lean_ctor_get(v_v_148_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_v_148_);
if (v_isSharedCheck_179_ == 0)
{
v___x_171_ = v_v_148_;
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_node_169_);
lean_dec(v_v_148_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_179_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
size_t v___x_173_; size_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_173_ = lean_usize_shift_right(v_x_133_, v___x_138_);
v___x_174_ = lean_usize_add(v_x_134_, v___x_139_);
v___x_175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_node_169_, v___x_173_, v___x_174_, v_x_135_, v_x_136_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_175_);
v___x_177_ = v___x_171_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
v___y_152_ = v___x_177_;
goto v___jp_151_;
}
}
}
default: 
{
lean_object* v___x_180_; 
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_x_135_);
lean_ctor_set(v___x_180_, 1, v_x_136_);
v___y_152_ = v___x_180_;
goto v___jp_151_;
}
}
v___jp_151_:
{
lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_153_ = lean_array_fset(v_xs_x27_150_, v_j_142_, v___y_152_);
lean_dec(v_j_142_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_153_);
v___x_155_ = v___x_146_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
}
}
else
{
lean_object* v_ks_183_; lean_object* v_vs_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_204_; 
v_ks_183_ = lean_ctor_get(v_x_132_, 0);
v_vs_184_ = lean_ctor_get(v_x_132_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_x_132_);
if (v_isSharedCheck_204_ == 0)
{
v___x_186_ = v_x_132_;
v_isShared_187_ = v_isSharedCheck_204_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_vs_184_);
lean_inc(v_ks_183_);
lean_dec(v_x_132_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_204_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_ks_183_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_vs_184_);
v___x_189_ = v_reuseFailAlloc_203_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v_newNode_190_; uint8_t v___y_192_; size_t v___x_198_; uint8_t v___x_199_; 
v_newNode_190_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(v___x_189_, v_x_135_, v_x_136_);
v___x_198_ = ((size_t)7ULL);
v___x_199_ = lean_usize_dec_le(v___x_198_, v_x_134_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_200_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_190_);
v___x_201_ = lean_unsigned_to_nat(4u);
v___x_202_ = lean_nat_dec_lt(v___x_200_, v___x_201_);
lean_dec(v___x_200_);
v___y_192_ = v___x_202_;
goto v___jp_191_;
}
else
{
v___y_192_ = v___x_199_;
goto v___jp_191_;
}
v___jp_191_:
{
if (v___y_192_ == 0)
{
lean_object* v_ks_193_; lean_object* v_vs_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_ks_193_ = lean_ctor_get(v_newNode_190_, 0);
lean_inc_ref(v_ks_193_);
v_vs_194_ = lean_ctor_get(v_newNode_190_, 1);
lean_inc_ref(v_vs_194_);
lean_dec_ref(v_newNode_190_);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_197_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_x_134_, v_ks_193_, v_vs_194_, v___x_195_, v___x_196_);
lean_dec_ref(v_vs_194_);
lean_dec_ref(v_ks_193_);
return v___x_197_;
}
else
{
return v_newNode_190_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(size_t v_depth_205_, lean_object* v_keys_206_, lean_object* v_vals_207_, lean_object* v_i_208_, lean_object* v_entries_209_){
_start:
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_array_get_size(v_keys_206_);
v___x_211_ = lean_nat_dec_lt(v_i_208_, v___x_210_);
if (v___x_211_ == 0)
{
lean_dec(v_i_208_);
return v_entries_209_;
}
else
{
lean_object* v_k_212_; lean_object* v_v_213_; uint64_t v___x_214_; size_t v_h_215_; size_t v___x_216_; lean_object* v___x_217_; size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v_h_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_k_212_ = lean_array_fget_borrowed(v_keys_206_, v_i_208_);
v_v_213_ = lean_array_fget_borrowed(v_vals_207_, v_i_208_);
v___x_214_ = l_Lean_instHashableMVarId_hash(v_k_212_);
v_h_215_ = lean_uint64_to_usize(v___x_214_);
v___x_216_ = ((size_t)5ULL);
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = ((size_t)1ULL);
v___x_219_ = lean_usize_sub(v_depth_205_, v___x_218_);
v___x_220_ = lean_usize_mul(v___x_216_, v___x_219_);
v_h_221_ = lean_usize_shift_right(v_h_215_, v___x_220_);
v___x_222_ = lean_nat_add(v_i_208_, v___x_217_);
lean_dec(v_i_208_);
lean_inc(v_v_213_);
lean_inc(v_k_212_);
v___x_223_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_entries_209_, v_h_221_, v_depth_205_, v_k_212_, v_v_213_);
v_i_208_ = v___x_222_;
v_entries_209_ = v___x_223_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_depth_225_, lean_object* v_keys_226_, lean_object* v_vals_227_, lean_object* v_i_228_, lean_object* v_entries_229_){
_start:
{
size_t v_depth_boxed_230_; lean_object* v_res_231_; 
v_depth_boxed_230_ = lean_unbox_usize(v_depth_225_);
lean_dec(v_depth_225_);
v_res_231_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_230_, v_keys_226_, v_vals_227_, v_i_228_, v_entries_229_);
lean_dec_ref(v_vals_227_);
lean_dec_ref(v_keys_226_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_232_, lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_x_236_){
_start:
{
size_t v_x_3614__boxed_237_; size_t v_x_3615__boxed_238_; lean_object* v_res_239_; 
v_x_3614__boxed_237_ = lean_unbox_usize(v_x_233_);
lean_dec(v_x_233_);
v_x_3615__boxed_238_ = lean_unbox_usize(v_x_234_);
lean_dec(v_x_234_);
v_res_239_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_232_, v_x_3614__boxed_237_, v_x_3615__boxed_238_, v_x_235_, v_x_236_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(lean_object* v_x_240_, lean_object* v_x_241_, lean_object* v_x_242_){
_start:
{
uint64_t v___x_243_; size_t v___x_244_; size_t v___x_245_; lean_object* v___x_246_; 
v___x_243_ = l_Lean_instHashableMVarId_hash(v_x_241_);
v___x_244_ = lean_uint64_to_usize(v___x_243_);
v___x_245_ = ((size_t)1ULL);
v___x_246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_240_, v___x_244_, v___x_245_, v_x_241_, v_x_242_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(lean_object* v_mvarId_247_, lean_object* v_val_248_, lean_object* v___y_249_){
_start:
{
lean_object* v___x_251_; lean_object* v_mctx_252_; lean_object* v_cache_253_; lean_object* v_zetaDeltaFVarIds_254_; lean_object* v_postponed_255_; lean_object* v_diag_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_283_; 
v___x_251_ = lean_st_ref_take(v___y_249_);
v_mctx_252_ = lean_ctor_get(v___x_251_, 0);
v_cache_253_ = lean_ctor_get(v___x_251_, 1);
v_zetaDeltaFVarIds_254_ = lean_ctor_get(v___x_251_, 2);
v_postponed_255_ = lean_ctor_get(v___x_251_, 3);
v_diag_256_ = lean_ctor_get(v___x_251_, 4);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_283_ == 0)
{
v___x_258_ = v___x_251_;
v_isShared_259_ = v_isSharedCheck_283_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_diag_256_);
lean_inc(v_postponed_255_);
lean_inc(v_zetaDeltaFVarIds_254_);
lean_inc(v_cache_253_);
lean_inc(v_mctx_252_);
lean_dec(v___x_251_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_283_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_depth_260_; lean_object* v_levelAssignDepth_261_; lean_object* v_mvarCounter_262_; lean_object* v_lDepth_263_; lean_object* v_decls_264_; lean_object* v_userNames_265_; lean_object* v_lAssignment_266_; lean_object* v_eAssignment_267_; lean_object* v_dAssignment_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_282_; 
v_depth_260_ = lean_ctor_get(v_mctx_252_, 0);
v_levelAssignDepth_261_ = lean_ctor_get(v_mctx_252_, 1);
v_mvarCounter_262_ = lean_ctor_get(v_mctx_252_, 2);
v_lDepth_263_ = lean_ctor_get(v_mctx_252_, 3);
v_decls_264_ = lean_ctor_get(v_mctx_252_, 4);
v_userNames_265_ = lean_ctor_get(v_mctx_252_, 5);
v_lAssignment_266_ = lean_ctor_get(v_mctx_252_, 6);
v_eAssignment_267_ = lean_ctor_get(v_mctx_252_, 7);
v_dAssignment_268_ = lean_ctor_get(v_mctx_252_, 8);
v_isSharedCheck_282_ = !lean_is_exclusive(v_mctx_252_);
if (v_isSharedCheck_282_ == 0)
{
v___x_270_ = v_mctx_252_;
v_isShared_271_ = v_isSharedCheck_282_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_dAssignment_268_);
lean_inc(v_eAssignment_267_);
lean_inc(v_lAssignment_266_);
lean_inc(v_userNames_265_);
lean_inc(v_decls_264_);
lean_inc(v_lDepth_263_);
lean_inc(v_mvarCounter_262_);
lean_inc(v_levelAssignDepth_261_);
lean_inc(v_depth_260_);
lean_dec(v_mctx_252_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_282_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(v_eAssignment_267_, v_mvarId_247_, v_val_248_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 7, v___x_272_);
v___x_274_ = v___x_270_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_depth_260_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_levelAssignDepth_261_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_mvarCounter_262_);
lean_ctor_set(v_reuseFailAlloc_281_, 3, v_lDepth_263_);
lean_ctor_set(v_reuseFailAlloc_281_, 4, v_decls_264_);
lean_ctor_set(v_reuseFailAlloc_281_, 5, v_userNames_265_);
lean_ctor_set(v_reuseFailAlloc_281_, 6, v_lAssignment_266_);
lean_ctor_set(v_reuseFailAlloc_281_, 7, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_281_, 8, v_dAssignment_268_);
v___x_274_ = v_reuseFailAlloc_281_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_276_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 0, v___x_274_);
v___x_276_ = v___x_258_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_274_);
lean_ctor_set(v_reuseFailAlloc_280_, 1, v_cache_253_);
lean_ctor_set(v_reuseFailAlloc_280_, 2, v_zetaDeltaFVarIds_254_);
lean_ctor_set(v_reuseFailAlloc_280_, 3, v_postponed_255_);
lean_ctor_set(v_reuseFailAlloc_280_, 4, v_diag_256_);
v___x_276_ = v_reuseFailAlloc_280_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_st_ref_set(v___y_249_, v___x_276_);
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg___boxed(lean_object* v_mvarId_284_, lean_object* v_val_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvarId_284_, v_val_285_, v___y_286_);
lean_dec(v___y_286_);
return v_res_288_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0));
v___x_291_ = l_Lean_stringToMessageData(v___x_290_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8));
v___x_304_ = l_Lean_stringToMessageData(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(lean_object* v_mvar_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___x_318_; 
lean_inc(v_mvar_305_);
v___x_318_ = l_Lean_MVarId_getType(v_mvar_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; lean_object* v_a_321_; lean_object* v___x_322_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref(v___x_318_);
v___x_320_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_a_319_, v_a_307_);
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref(v___x_320_);
v___x_322_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_321_);
lean_dec(v_a_321_);
if (lean_obj_tag(v___x_322_) == 1)
{
lean_object* v_val_323_; lean_object* v_target_324_; 
v_val_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_val_323_);
lean_dec_ref(v___x_322_);
v_target_324_ = lean_ctor_get(v_val_323_, 3);
lean_inc_ref(v_target_324_);
if (lean_obj_tag(v_target_324_) == 5)
{
lean_object* v_fn_325_; 
v_fn_325_ = lean_ctor_get(v_target_324_, 0);
lean_inc_ref(v_fn_325_);
if (lean_obj_tag(v_fn_325_) == 5)
{
lean_object* v_fn_326_; 
v_fn_326_ = lean_ctor_get(v_fn_325_, 0);
lean_inc_ref(v_fn_326_);
if (lean_obj_tag(v_fn_326_) == 5)
{
lean_object* v_fn_327_; 
v_fn_327_ = lean_ctor_get(v_fn_326_, 0);
if (lean_obj_tag(v_fn_327_) == 4)
{
lean_object* v_declName_328_; 
v_declName_328_ = lean_ctor_get(v_fn_327_, 0);
lean_inc(v_declName_328_);
if (lean_obj_tag(v_declName_328_) == 1)
{
lean_object* v_pre_329_; 
v_pre_329_ = lean_ctor_get(v_declName_328_, 0);
lean_inc(v_pre_329_);
if (lean_obj_tag(v_pre_329_) == 1)
{
lean_object* v_pre_330_; 
v_pre_330_ = lean_ctor_get(v_pre_329_, 0);
lean_inc(v_pre_330_);
if (lean_obj_tag(v_pre_330_) == 1)
{
lean_object* v_pre_331_; 
v_pre_331_ = lean_ctor_get(v_pre_330_, 0);
lean_inc(v_pre_331_);
if (lean_obj_tag(v_pre_331_) == 1)
{
lean_object* v_pre_332_; 
v_pre_332_ = lean_ctor_get(v_pre_331_, 0);
lean_inc(v_pre_332_);
if (lean_obj_tag(v_pre_332_) == 0)
{
lean_object* v_u_333_; lean_object* v_00_u03c3s_334_; lean_object* v_hyps_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_397_; 
v_u_333_ = lean_ctor_get(v_val_323_, 0);
v_00_u03c3s_334_ = lean_ctor_get(v_val_323_, 1);
v_hyps_335_ = lean_ctor_get(v_val_323_, 2);
v_isSharedCheck_397_ = !lean_is_exclusive(v_val_323_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v_val_323_, 3);
lean_dec(v_unused_398_);
v___x_337_ = v_val_323_;
v_isShared_338_ = v_isSharedCheck_397_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_hyps_335_);
lean_inc(v_00_u03c3s_334_);
lean_inc(v_u_333_);
lean_dec(v_val_323_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_397_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v_arg_339_; lean_object* v_arg_340_; lean_object* v_arg_341_; lean_object* v_str_342_; lean_object* v_str_343_; lean_object* v_str_344_; lean_object* v_str_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_arg_339_ = lean_ctor_get(v_target_324_, 1);
lean_inc_ref(v_arg_339_);
lean_dec_ref(v_target_324_);
v_arg_340_ = lean_ctor_get(v_fn_325_, 1);
lean_inc_ref(v_arg_340_);
lean_dec_ref(v_fn_325_);
v_arg_341_ = lean_ctor_get(v_fn_326_, 1);
lean_inc_ref(v_arg_341_);
lean_dec_ref(v_fn_326_);
v_str_342_ = lean_ctor_get(v_declName_328_, 1);
lean_inc_ref(v_str_342_);
lean_dec_ref(v_declName_328_);
v_str_343_ = lean_ctor_get(v_pre_329_, 1);
lean_inc_ref(v_str_343_);
lean_dec_ref(v_pre_329_);
v_str_344_ = lean_ctor_get(v_pre_330_, 1);
lean_inc_ref(v_str_344_);
lean_dec_ref(v_pre_330_);
v_str_345_ = lean_ctor_get(v_pre_331_, 1);
lean_inc_ref(v_str_345_);
lean_dec_ref(v_pre_331_);
v___x_346_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2));
v___x_347_ = lean_string_dec_eq(v_str_345_, v___x_346_);
lean_dec_ref(v_str_345_);
if (v___x_347_ == 0)
{
lean_dec_ref(v_str_344_);
lean_dec_ref(v_str_343_);
lean_dec_ref(v_str_342_);
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_339_);
lean_del_object(v___x_337_);
lean_dec_ref(v_hyps_335_);
lean_dec_ref(v_00_u03c3s_334_);
lean_dec(v_u_333_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
else
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3));
v___x_349_ = lean_string_dec_eq(v_str_344_, v___x_348_);
lean_dec_ref(v_str_344_);
if (v___x_349_ == 0)
{
lean_dec_ref(v_str_343_);
lean_dec_ref(v_str_342_);
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_339_);
lean_del_object(v___x_337_);
lean_dec_ref(v_hyps_335_);
lean_dec_ref(v_00_u03c3s_334_);
lean_dec(v_u_333_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
else
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4));
v___x_351_ = lean_string_dec_eq(v_str_343_, v___x_350_);
lean_dec_ref(v_str_343_);
if (v___x_351_ == 0)
{
lean_dec_ref(v_str_342_);
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_339_);
lean_del_object(v___x_337_);
lean_dec_ref(v_hyps_335_);
lean_dec_ref(v_00_u03c3s_334_);
lean_dec(v_u_333_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
else
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5));
v___x_353_ = lean_string_dec_eq(v_str_342_, v___x_352_);
lean_dec_ref(v_str_342_);
if (v___x_353_ == 0)
{
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_339_);
lean_del_object(v___x_337_);
lean_dec_ref(v_hyps_335_);
lean_dec_ref(v_00_u03c3s_334_);
lean_dec(v_u_333_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
else
{
lean_object* v___x_355_; 
lean_inc_ref(v_arg_340_);
lean_inc_ref(v_hyps_335_);
lean_inc_ref(v_00_u03c3s_334_);
lean_inc(v_u_333_);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 3, v_arg_340_);
v___x_355_ = v___x_337_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_u_333_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_00_u03c3s_334_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_hyps_335_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_arg_340_);
v___x_355_ = v_reuseFailAlloc_396_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_355_);
lean_inc_ref(v_a_306_);
v___x_357_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_356_, v_pre_332_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
lean_inc_ref(v_arg_339_);
lean_inc_ref(v_hyps_335_);
lean_inc(v_u_333_);
v___x_359_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_359_, 0, v_u_333_);
lean_ctor_set(v___x_359_, 1, v_00_u03c3s_334_);
lean_ctor_set(v___x_359_, 2, v_hyps_335_);
lean_ctor_set(v___x_359_, 3, v_arg_339_);
v___x_360_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_359_);
v___x_361_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_360_, v_pre_332_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_378_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref(v___x_361_);
v___x_363_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7));
v___x_364_ = lean_box(0);
v___x_365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_365_, 0, v_u_333_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = l_Lean_mkConst(v___x_363_, v___x_365_);
lean_inc(v_a_362_);
lean_inc(v_a_358_);
v___x_367_ = l_Lean_mkApp6(v___x_366_, v_arg_341_, v_hyps_335_, v_arg_340_, v_arg_339_, v_a_358_, v_a_362_);
v___x_368_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvar_305_, v___x_367_, v_a_307_);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_378_ == 0)
{
lean_object* v_unused_379_; 
v_unused_379_ = lean_ctor_get(v___x_368_, 0);
lean_dec(v_unused_379_);
v___x_370_ = v___x_368_;
v_isShared_371_ = v_isSharedCheck_378_;
goto v_resetjp_369_;
}
else
{
lean_dec(v___x_368_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_378_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_372_ = l_Lean_Expr_mvarId_x21(v_a_358_);
lean_dec(v_a_358_);
v___x_373_ = l_Lean_Expr_mvarId_x21(v_a_362_);
lean_dec(v_a_362_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
if (v_isShared_371_ == 0)
{
lean_ctor_set(v___x_370_, 0, v___x_374_);
v___x_376_ = v___x_370_;
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
lean_dec(v_a_358_);
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_hyps_335_);
lean_dec(v_u_333_);
lean_dec(v_mvar_305_);
v_a_380_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_361_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_361_);
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
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec_ref(v_arg_341_);
lean_dec_ref(v_arg_340_);
lean_dec_ref(v_arg_339_);
lean_dec_ref(v_hyps_335_);
lean_dec_ref(v_00_u03c3s_334_);
lean_dec(v_u_333_);
lean_dec_ref(v_a_306_);
lean_dec(v_mvar_305_);
v_a_388_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_357_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_357_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
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
else
{
lean_dec_ref(v_pre_331_);
lean_dec(v_pre_332_);
lean_dec_ref(v_pre_330_);
lean_dec_ref(v_pre_329_);
lean_dec_ref(v_declName_328_);
lean_dec_ref(v_fn_326_);
lean_dec_ref(v_fn_325_);
lean_dec_ref(v_target_324_);
lean_dec(v_val_323_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
}
else
{
lean_dec(v_pre_331_);
lean_dec_ref(v_pre_330_);
lean_dec_ref(v_pre_329_);
lean_dec_ref(v_declName_328_);
lean_dec_ref(v_fn_326_);
lean_dec_ref(v_fn_325_);
lean_dec_ref(v_target_324_);
lean_dec(v_val_323_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
}
else
{
lean_dec_ref(v_pre_329_);
lean_dec(v_pre_330_);
lean_dec_ref(v_declName_328_);
lean_dec_ref(v_fn_326_);
lean_dec_ref(v_fn_325_);
lean_dec_ref(v_target_324_);
lean_dec(v_val_323_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
}
else
{
lean_dec(v_pre_329_);
lean_dec_ref(v_declName_328_);
lean_dec_ref(v_fn_326_);
lean_dec_ref(v_fn_325_);
lean_dec_ref(v_target_324_);
lean_dec(v_val_323_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
}
else
{
lean_dec(v_declName_328_);
lean_dec_ref(v_fn_326_);
lean_dec_ref(v_fn_325_);
lean_dec_ref(v_target_324_);
lean_dec(v_val_323_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
}
else
{
lean_dec_ref(v_fn_326_);
lean_dec_ref(v_fn_325_);
lean_dec_ref(v_target_324_);
lean_dec(v_val_323_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
}
else
{
lean_dec_ref(v_fn_325_);
lean_dec_ref(v_fn_326_);
lean_dec_ref(v_target_324_);
lean_dec(v_val_323_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
}
else
{
lean_dec_ref(v_target_324_);
lean_dec_ref(v_fn_325_);
lean_dec(v_val_323_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
}
else
{
lean_dec_ref(v_target_324_);
lean_dec(v_val_323_);
lean_dec(v_mvar_305_);
v___y_312_ = v_a_306_;
v___y_313_ = v_a_307_;
v___y_314_ = v_a_308_;
v___y_315_ = v_a_309_;
goto v___jp_311_;
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec(v___x_322_);
lean_dec(v_mvar_305_);
v___x_399_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9, &l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9);
v___x_400_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v___x_399_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
lean_dec_ref(v_a_306_);
return v___x_400_;
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
lean_dec_ref(v_a_306_);
lean_dec(v_mvar_305_);
v_a_401_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_408_ == 0)
{
v___x_403_ = v___x_318_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_318_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_401_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
v___jp_311_:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1);
v___x_317_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v___x_316_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec_ref(v___y_312_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___boxed(lean_object* v_mvar_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(v_mvar_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
lean_dec(v_a_411_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0(lean_object* v_00_u03b1_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v_msg_417_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___boxed(lean_object* v_00_u03b1_424_, lean_object* v_msg_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0(v_00_u03b1_424_, v_msg_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2(lean_object* v_mvarId_432_, lean_object* v_val_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvarId_432_, v_val_433_, v___y_435_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___boxed(lean_object* v_mvarId_440_, lean_object* v_val_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2(v_mvarId_440_, v_val_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3(lean_object* v_00_u03b2_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(v_x_449_, v_x_450_, v_x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_453_, lean_object* v_x_454_, size_t v_x_455_, size_t v_x_456_, lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_454_, v_x_455_, v_x_456_, v_x_457_, v_x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_460_, lean_object* v_x_461_, lean_object* v_x_462_, lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
size_t v_x_4130__boxed_466_; size_t v_x_4131__boxed_467_; lean_object* v_res_468_; 
v_x_4130__boxed_466_ = lean_unbox_usize(v_x_462_);
lean_dec(v_x_462_);
v_x_4131__boxed_467_ = lean_unbox_usize(v_x_463_);
lean_dec(v_x_463_);
v_res_468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4(v_00_u03b2_460_, v_x_461_, v_x_4130__boxed_466_, v_x_4131__boxed_467_, v_x_464_, v_x_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_469_, lean_object* v_n_470_, lean_object* v_k_471_, lean_object* v_v_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(v_n_470_, v_k_471_, v_v_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_474_, size_t v_depth_475_, lean_object* v_keys_476_, lean_object* v_vals_477_, lean_object* v_heq_478_, lean_object* v_i_479_, lean_object* v_entries_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_475_, v_keys_476_, v_vals_477_, v_i_479_, v_entries_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_482_, lean_object* v_depth_483_, lean_object* v_keys_484_, lean_object* v_vals_485_, lean_object* v_heq_486_, lean_object* v_i_487_, lean_object* v_entries_488_){
_start:
{
size_t v_depth_boxed_489_; lean_object* v_res_490_; 
v_depth_boxed_489_ = lean_unbox_usize(v_depth_483_);
lean_dec(v_depth_483_);
v_res_490_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_482_, v_depth_boxed_489_, v_keys_484_, v_vals_485_, v_heq_486_, v_i_487_, v_entries_488_);
lean_dec_ref(v_vals_485_);
lean_dec_ref(v_keys_484_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_491_, lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_492_, v_x_493_, v_x_494_, v_x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0(lean_object* v_x_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_apply_9(v_x_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, lean_box(0));
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0___boxed(lean_object* v_x_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0(v_x_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(lean_object* v_mvarId_519_, lean_object* v_x_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___f_530_; lean_object* v___x_531_; 
v___f_530_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_530_, 0, v_x_520_);
lean_closure_set(v___f_530_, 1, v___y_521_);
lean_closure_set(v___f_530_, 2, v___y_522_);
lean_closure_set(v___f_530_, 3, v___y_523_);
lean_closure_set(v___f_530_, 4, v___y_524_);
v___x_531_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_519_, v___f_530_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
if (lean_obj_tag(v___x_531_) == 0)
{
return v___x_531_;
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___boxed(lean_object* v_mvarId_540_, lean_object* v_x_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_mvarId_540_, v_x_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0(lean_object* v_00_u03b1_552_, lean_object* v_mvarId_553_, lean_object* v_x_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_mvarId_553_, v_x_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___boxed(lean_object* v_00_u03b1_565_, lean_object* v_mvarId_566_, lean_object* v_x_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0(v_00_u03b1_565_, v_mvarId_566_, v_x_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0(lean_object* v_a_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v___x_588_; 
lean_inc_ref(v___y_583_);
v___x_588_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(v_a_578_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v_fst_590_; lean_object* v_snd_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_601_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref(v___x_588_);
v_fst_590_ = lean_ctor_get(v_a_589_, 0);
v_snd_591_ = lean_ctor_get(v_a_589_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_a_589_);
if (v_isSharedCheck_601_ == 0)
{
v___x_593_ = v_a_589_;
v_isShared_594_ = v_isSharedCheck_601_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_snd_591_);
lean_inc(v_fst_590_);
lean_dec(v_a_589_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_601_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = lean_box(0);
if (v_isShared_594_ == 0)
{
lean_ctor_set_tag(v___x_593_, 1);
lean_ctor_set(v___x_593_, 1, v___x_595_);
lean_ctor_set(v___x_593_, 0, v_snd_591_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_snd_591_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_595_);
v___x_597_ = v_reuseFailAlloc_600_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_598_, 0, v_fst_590_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_598_, v___y_580_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec_ref(v___y_583_);
return v___x_599_;
}
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec_ref(v___y_583_);
v_a_602_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_588_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_588_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0___boxed(lean_object* v_a_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0(v_a_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_622_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___f_632_; lean_object* v___x_633_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_a_631_);
lean_dec_ref(v___x_630_);
lean_inc(v_a_631_);
v___f_632_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_632_, 0, v_a_631_);
v___x_633_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_a_631_, v___f_632_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
return v___x_633_;
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
v_a_634_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_630_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_630_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___boxed(lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(v_a_642_, v_a_643_, v_a_644_, v_a_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor(lean_object* v_x_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___boxed(lean_object* v_x_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor(v_x_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec(v_x_663_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1(){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_694_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_695_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4));
v___x_696_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8));
v___x_697_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___boxed), 10, 0);
v___x_698_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_694_, v___x_695_, v___x_696_, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___boxed(lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1();
return v_res_700_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_Do_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(builtin);
}
#ifdef __cplusplus
}
#endif
