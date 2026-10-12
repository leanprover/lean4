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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0;
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "mconstructor"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(115, 154, 195, 216, 142, 75, 110, 212)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elabMConstructor"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(14, 68, 128, 8, 115, 239, 72, 179)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___boxed(lean_object*);
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(lean_object* v_msgData_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v___x_52_; lean_object* v_env_53_; uint8_t v___x_54_; lean_object* v_env_55_; lean_object* v___x_56_; lean_object* v_toCold_57_; lean_object* v_mctx_58_; lean_object* v_lctx_59_; lean_object* v_options_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_52_ = lean_st_ref_get(v___y_50_);
v_env_53_ = lean_ctor_get(v___x_52_, 0);
lean_inc_ref(v_env_53_);
lean_dec(v___x_52_);
v___x_54_ = 0;
v_env_55_ = l_Lean_Environment_setRecordingDeps(v_env_53_, v___x_54_);
v___x_56_ = lean_st_ref_get(v___y_48_);
v_toCold_57_ = lean_ctor_get(v___y_49_, 0);
v_mctx_58_ = lean_ctor_get(v___x_56_, 0);
lean_inc_ref(v_mctx_58_);
lean_dec(v___x_56_);
v_lctx_59_ = lean_ctor_get(v___y_47_, 2);
v_options_60_ = lean_ctor_get(v_toCold_57_, 2);
lean_inc_ref(v_options_60_);
lean_inc_ref(v_lctx_59_);
v___x_61_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_61_, 0, v_env_55_);
lean_ctor_set(v___x_61_, 1, v_mctx_58_);
lean_ctor_set(v___x_61_, 2, v_lctx_59_);
lean_ctor_set(v___x_61_, 3, v_options_60_);
v___x_62_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v_msgData_46_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_46_ = stack[0].m_obj;
lean_object* v___y_47_ = stack[1].m_obj;
lean_object* v___y_48_ = stack[2].m_obj;
lean_object* v___y_49_ = stack[3].m_obj;
lean_object* v___y_50_ = stack[4].m_obj;
lean_object* v_res_64_;
v_res_64_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(v_msgData_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
stack->m_obj
 = v_res_64_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0___boxed(lean_object* v_msgData_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(v_msgData_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
return v_res_71_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(lean_object* v_msg_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_ref_78_; lean_object* v___x_79_; lean_object* v_a_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_88_; 
v_ref_78_ = lean_ctor_get(v___y_75_, 2);
v___x_79_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_spec__0(v_msg_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
v_a_80_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_88_ == 0)
{
v___x_82_ = v___x_79_;
v_isShared_83_ = v_isSharedCheck_88_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_a_80_);
lean_dec(v___x_79_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_88_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
lean_object* v___x_84_; lean_object* v___x_86_; 
lean_inc(v_ref_78_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v_ref_78_);
lean_ctor_set(v___x_84_, 1, v_a_80_);
if (v_isShared_83_ == 0)
{
lean_ctor_set_tag(v___x_82_, 1);
lean_ctor_set(v___x_82_, 0, v___x_84_);
v___x_86_ = v___x_82_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_84_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_72_ = stack[0].m_obj;
lean_object* v___y_73_ = stack[1].m_obj;
lean_object* v___y_74_ = stack[2].m_obj;
lean_object* v___y_75_ = stack[3].m_obj;
lean_object* v___y_76_ = stack[4].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v_msg_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg___boxed(lean_object* v_msg_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v_msg_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_x_97_, lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
lean_object* v_ks_101_; lean_object* v_vs_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_126_; 
v_ks_101_ = lean_ctor_get(v_x_97_, 0);
v_vs_102_ = lean_ctor_get(v_x_97_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_x_97_);
if (v_isSharedCheck_126_ == 0)
{
v___x_104_ = v_x_97_;
v_isShared_105_ = v_isSharedCheck_126_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_vs_102_);
lean_inc(v_ks_101_);
lean_dec(v_x_97_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_126_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_array_get_size(v_ks_101_);
v___x_107_ = lean_nat_dec_lt(v_x_98_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
lean_dec(v_x_98_);
v___x_108_ = lean_array_push(v_ks_101_, v_x_99_);
v___x_109_ = lean_array_push(v_vs_102_, v_x_100_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_109_);
lean_ctor_set(v___x_104_, 0, v___x_108_);
v___x_111_ = v___x_104_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
else
{
lean_object* v_k_x27_113_; uint8_t v___x_114_; 
v_k_x27_113_ = lean_array_fget_borrowed(v_ks_101_, v_x_98_);
v___x_114_ = l_Lean_instBEqMVarId_beq(v_x_99_, v_k_x27_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_116_; 
if (v_isShared_105_ == 0)
{
v___x_116_ = v___x_104_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_ks_101_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v_vs_102_);
v___x_116_ = v_reuseFailAlloc_120_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(1u);
v___x_118_ = lean_nat_add(v_x_98_, v___x_117_);
lean_dec(v_x_98_);
v_x_97_ = v___x_116_;
v_x_98_ = v___x_118_;
goto _start;
}
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_121_ = lean_array_fset(v_ks_101_, v_x_98_, v_x_99_);
v___x_122_ = lean_array_fset(v_vs_102_, v_x_98_, v_x_100_);
lean_dec(v_x_98_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_122_);
lean_ctor_set(v___x_104_, 0, v___x_121_);
v___x_124_ = v___x_104_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_n_127_, lean_object* v_k_128_, lean_object* v_v_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_127_, v___x_130_, v_k_128_, v_v_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_132_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(lean_object* v_x_133_, size_t v_x_134_, size_t v_x_135_, lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_object* v_es_138_; size_t v___x_139_; size_t v___x_140_; lean_object* v_j_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_es_138_ = lean_ctor_get(v_x_133_, 0);
v___x_139_ = ((size_t)31ULL);
v___x_140_ = lean_usize_land(v_x_134_, v___x_139_);
v_j_141_ = lean_usize_to_nat(v___x_140_);
v___x_142_ = lean_array_get_size(v_es_138_);
v___x_143_ = lean_nat_dec_lt(v_j_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_dec(v_j_141_);
lean_dec(v_x_137_);
lean_dec(v_x_136_);
return v_x_133_;
}
else
{
lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_182_; 
lean_inc_ref(v_es_138_);
v_isSharedCheck_182_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_182_ == 0)
{
lean_object* v_unused_183_; 
v_unused_183_ = lean_ctor_get(v_x_133_, 0);
lean_dec(v_unused_183_);
v___x_145_ = v_x_133_;
v_isShared_146_ = v_isSharedCheck_182_;
goto v_resetjp_144_;
}
else
{
lean_dec(v_x_133_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_182_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v_v_147_; lean_object* v___x_148_; lean_object* v_xs_x27_149_; lean_object* v___y_151_; 
v_v_147_ = lean_array_fget(v_es_138_, v_j_141_);
v___x_148_ = lean_box(0);
v_xs_x27_149_ = lean_array_fset(v_es_138_, v_j_141_, v___x_148_);
switch(lean_obj_tag(v_v_147_))
{
case 0:
{
lean_object* v_key_156_; lean_object* v_val_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_167_; 
v_key_156_ = lean_ctor_get(v_v_147_, 0);
v_val_157_ = lean_ctor_get(v_v_147_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_v_147_);
if (v_isSharedCheck_167_ == 0)
{
v___x_159_ = v_v_147_;
v_isShared_160_ = v_isSharedCheck_167_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_val_157_);
lean_inc(v_key_156_);
lean_dec(v_v_147_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_167_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
uint8_t v___x_161_; 
v___x_161_ = l_Lean_instBEqMVarId_beq(v_x_136_, v_key_156_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_del_object(v___x_159_);
v___x_162_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_156_, v_val_157_, v_x_136_, v_x_137_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
v___y_151_ = v___x_163_;
goto v___jp_150_;
}
else
{
lean_object* v___x_165_; 
lean_dec(v_val_157_);
lean_dec(v_key_156_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v_x_137_);
lean_ctor_set(v___x_159_, 0, v_x_136_);
v___x_165_ = v___x_159_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_x_136_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_x_137_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
v___y_151_ = v___x_165_;
goto v___jp_150_;
}
}
}
}
case 1:
{
lean_object* v_node_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_180_; 
v_node_168_ = lean_ctor_get(v_v_147_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_v_147_);
if (v_isSharedCheck_180_ == 0)
{
v___x_170_ = v_v_147_;
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_node_168_);
lean_dec(v_v_147_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_180_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_178_; 
v___x_172_ = ((size_t)5ULL);
v___x_173_ = lean_usize_shift_right(v_x_134_, v___x_172_);
v___x_174_ = ((size_t)1ULL);
v___x_175_ = lean_usize_add(v_x_135_, v___x_174_);
v___x_176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_node_168_, v___x_173_, v___x_175_, v_x_136_, v_x_137_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_176_);
v___x_178_ = v___x_170_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
v___y_151_ = v___x_178_;
goto v___jp_150_;
}
}
}
default: 
{
lean_object* v___x_181_; 
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v_x_136_);
lean_ctor_set(v___x_181_, 1, v_x_137_);
v___y_151_ = v___x_181_;
goto v___jp_150_;
}
}
v___jp_150_:
{
lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_152_ = lean_array_fset(v_xs_x27_149_, v_j_141_, v___y_151_);
lean_dec(v_j_141_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_152_);
v___x_154_ = v___x_145_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
else
{
lean_object* v_ks_184_; lean_object* v_vs_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_203_; 
v_ks_184_ = lean_ctor_get(v_x_133_, 0);
v_vs_185_ = lean_ctor_get(v_x_133_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_203_ == 0)
{
v___x_187_ = v_x_133_;
v_isShared_188_ = v_isSharedCheck_203_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_vs_185_);
lean_inc(v_ks_184_);
lean_dec(v_x_133_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_203_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_ks_184_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_vs_185_);
v___x_190_ = v_reuseFailAlloc_202_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v_newNode_191_; size_t v___x_192_; uint8_t v___x_193_; 
v_newNode_191_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(v___x_190_, v_x_136_, v_x_137_);
v___x_192_ = ((size_t)7ULL);
v___x_193_ = lean_usize_dec_le(v___x_192_, v_x_135_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_194_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_191_);
v___x_195_ = lean_unsigned_to_nat(4u);
v___x_196_ = lean_nat_dec_lt(v___x_194_, v___x_195_);
lean_dec(v___x_194_);
if (v___x_196_ == 0)
{
lean_object* v_ks_197_; lean_object* v_vs_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_ks_197_ = lean_ctor_get(v_newNode_191_, 0);
lean_inc_ref(v_ks_197_);
v_vs_198_ = lean_ctor_get(v_newNode_191_, 1);
lean_inc_ref(v_vs_198_);
lean_dec_ref(v_newNode_191_);
v___x_199_ = lean_unsigned_to_nat(0u);
v___x_200_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_201_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_x_135_, v_ks_197_, v_vs_198_, v___x_199_, v___x_200_);
lean_dec_ref(v_vs_198_);
lean_dec_ref(v_ks_197_);
return v___x_201_;
}
else
{
return v_newNode_191_;
}
}
else
{
return v_newNode_191_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_133_ = stack[0].m_obj;
size_t v_x_134_ = stack[1].m_num;
size_t v_x_135_ = stack[2].m_num;
lean_object* v_x_136_ = stack[3].m_obj;
lean_object* v_x_137_ = stack[4].m_obj;
lean_object* v_res_204_;
v_res_204_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_133_, v_x_134_, v_x_135_, v_x_136_, v_x_137_);
stack->m_obj
 = v_res_204_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(size_t v_depth_205_, lean_object* v_keys_206_, lean_object* v_vals_207_, lean_object* v_i_208_, lean_object* v_entries_209_){
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
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_205_ = stack[0].m_num;
lean_object* v_keys_206_ = stack[1].m_obj;
lean_object* v_vals_207_ = stack[2].m_obj;
lean_object* v_i_208_ = stack[3].m_obj;
lean_object* v_entries_209_ = stack[4].m_obj;
lean_object* v_res_225_;
v_res_225_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_205_, v_keys_206_, v_vals_207_, v_i_208_, v_entries_209_);
stack->m_obj
 = v_res_225_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_depth_226_, lean_object* v_keys_227_, lean_object* v_vals_228_, lean_object* v_i_229_, lean_object* v_entries_230_){
_start:
{
size_t v_depth_boxed_231_; lean_object* v_res_232_; 
v_depth_boxed_231_ = lean_unbox_usize(v_depth_226_);
lean_dec(v_depth_226_);
v_res_232_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_231_, v_keys_227_, v_vals_228_, v_i_229_, v_entries_230_);
lean_dec_ref(v_vals_228_);
lean_dec_ref(v_keys_227_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
size_t v_x_3708__boxed_238_; size_t v_x_3709__boxed_239_; lean_object* v_res_240_; 
v_x_3708__boxed_238_ = lean_unbox_usize(v_x_234_);
lean_dec(v_x_234_);
v_x_3709__boxed_239_ = lean_unbox_usize(v_x_235_);
lean_dec(v_x_235_);
v_res_240_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_233_, v_x_3708__boxed_238_, v_x_3709__boxed_239_, v_x_236_, v_x_237_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
uint64_t v___x_244_; size_t v___x_245_; size_t v___x_246_; lean_object* v___x_247_; 
v___x_244_ = l_Lean_instHashableMVarId_hash(v_x_242_);
v___x_245_ = lean_uint64_to_usize(v___x_244_);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_241_, v___x_245_, v___x_246_, v_x_242_, v_x_243_);
return v___x_247_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(lean_object* v_mvarId_248_, lean_object* v_val_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; lean_object* v_mctx_253_; lean_object* v_cache_254_; lean_object* v_zetaDeltaFVarIds_255_; lean_object* v_postponed_256_; lean_object* v_diag_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_287_; 
v___x_252_ = lean_st_ref_take(v___y_250_);
v_mctx_253_ = lean_ctor_get(v___x_252_, 0);
v_cache_254_ = lean_ctor_get(v___x_252_, 1);
v_zetaDeltaFVarIds_255_ = lean_ctor_get(v___x_252_, 2);
v_postponed_256_ = lean_ctor_get(v___x_252_, 3);
v_diag_257_ = lean_ctor_get(v___x_252_, 4);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_287_ == 0)
{
v___x_259_ = v___x_252_;
v_isShared_260_ = v_isSharedCheck_287_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_diag_257_);
lean_inc(v_postponed_256_);
lean_inc(v_zetaDeltaFVarIds_255_);
lean_inc(v_cache_254_);
lean_inc(v_mctx_253_);
lean_dec(v___x_252_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_287_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v_depth_261_; lean_object* v_levelAssignDepth_262_; lean_object* v_lmvarCounter_263_; lean_object* v_mvarCounter_264_; lean_object* v_lDecls_265_; lean_object* v_decls_266_; lean_object* v_userNames_267_; lean_object* v_lAssignment_268_; lean_object* v_eAssignment_269_; lean_object* v_dAssignment_270_; lean_object* v_instanceTypedMVars_271_; lean_object* v_synthNormMemo_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_286_; 
v_depth_261_ = lean_ctor_get(v_mctx_253_, 0);
v_levelAssignDepth_262_ = lean_ctor_get(v_mctx_253_, 1);
v_lmvarCounter_263_ = lean_ctor_get(v_mctx_253_, 2);
v_mvarCounter_264_ = lean_ctor_get(v_mctx_253_, 3);
v_lDecls_265_ = lean_ctor_get(v_mctx_253_, 4);
v_decls_266_ = lean_ctor_get(v_mctx_253_, 5);
v_userNames_267_ = lean_ctor_get(v_mctx_253_, 6);
v_lAssignment_268_ = lean_ctor_get(v_mctx_253_, 7);
v_eAssignment_269_ = lean_ctor_get(v_mctx_253_, 8);
v_dAssignment_270_ = lean_ctor_get(v_mctx_253_, 9);
v_instanceTypedMVars_271_ = lean_ctor_get(v_mctx_253_, 10);
v_synthNormMemo_272_ = lean_ctor_get(v_mctx_253_, 11);
v_isSharedCheck_286_ = !lean_is_exclusive(v_mctx_253_);
if (v_isSharedCheck_286_ == 0)
{
v___x_274_ = v_mctx_253_;
v_isShared_275_ = v_isSharedCheck_286_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_synthNormMemo_272_);
lean_inc(v_instanceTypedMVars_271_);
lean_inc(v_dAssignment_270_);
lean_inc(v_eAssignment_269_);
lean_inc(v_lAssignment_268_);
lean_inc(v_userNames_267_);
lean_inc(v_decls_266_);
lean_inc(v_lDecls_265_);
lean_inc(v_mvarCounter_264_);
lean_inc(v_lmvarCounter_263_);
lean_inc(v_levelAssignDepth_262_);
lean_inc(v_depth_261_);
lean_dec(v_mctx_253_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_286_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_276_ = lean_box(0);
v___x_277_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(v_eAssignment_269_, v_mvarId_248_, v_val_249_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 8, v___x_277_);
v___x_279_ = v___x_274_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_depth_261_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_levelAssignDepth_262_);
lean_ctor_set(v_reuseFailAlloc_285_, 2, v_lmvarCounter_263_);
lean_ctor_set(v_reuseFailAlloc_285_, 3, v_mvarCounter_264_);
lean_ctor_set(v_reuseFailAlloc_285_, 4, v_lDecls_265_);
lean_ctor_set(v_reuseFailAlloc_285_, 5, v_decls_266_);
lean_ctor_set(v_reuseFailAlloc_285_, 6, v_userNames_267_);
lean_ctor_set(v_reuseFailAlloc_285_, 7, v_lAssignment_268_);
lean_ctor_set(v_reuseFailAlloc_285_, 8, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_285_, 9, v_dAssignment_270_);
lean_ctor_set(v_reuseFailAlloc_285_, 10, v_instanceTypedMVars_271_);
lean_ctor_set(v_reuseFailAlloc_285_, 11, v_synthNormMemo_272_);
v___x_279_ = v_reuseFailAlloc_285_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_281_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_279_);
v___x_281_ = v___x_259_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_cache_254_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_zetaDeltaFVarIds_255_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_postponed_256_);
lean_ctor_set(v_reuseFailAlloc_284_, 4, v_diag_257_);
v___x_281_ = v_reuseFailAlloc_284_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_st_ref_put(v___y_250_, v___x_281_);
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_276_);
return v___x_283_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_248_ = stack[0].m_obj;
lean_object* v_val_249_ = stack[1].m_obj;
lean_object* v___y_250_ = stack[2].m_obj;
lean_object* v_res_288_;
v_res_288_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvarId_248_, v_val_249_, v___y_250_);
stack->m_obj
 = v_res_288_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg___boxed(lean_object* v_mvarId_289_, lean_object* v_val_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvarId_289_, v_val_290_, v___y_291_);
lean_dec(v___y_291_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__0));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__8));
v___x_309_ = l_Lean_stringToMessageData(v___x_308_);
return v___x_309_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(lean_object* v_mvar_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___x_323_; 
lean_inc(v_mvar_310_);
v___x_323_ = l_Lean_MVarId_getType(v_mvar_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_325_; lean_object* v_a_326_; lean_object* v___x_327_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_323_, 1);
v___x_325_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__1___redArg(v_a_324_, v_a_312_);
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref(v___x_325_);
v___x_327_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_326_);
lean_dec(v_a_326_);
if (lean_obj_tag(v___x_327_) == 1)
{
lean_object* v_val_328_; lean_object* v_target_329_; 
v_val_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_val_328_);
lean_dec_ref_known(v___x_327_, 1);
v_target_329_ = lean_ctor_get(v_val_328_, 3);
lean_inc_ref(v_target_329_);
if (lean_obj_tag(v_target_329_) == 5)
{
lean_object* v_fn_330_; 
v_fn_330_ = lean_ctor_get(v_target_329_, 0);
lean_inc_ref(v_fn_330_);
if (lean_obj_tag(v_fn_330_) == 5)
{
lean_object* v_fn_331_; 
v_fn_331_ = lean_ctor_get(v_fn_330_, 0);
lean_inc_ref(v_fn_331_);
if (lean_obj_tag(v_fn_331_) == 5)
{
lean_object* v_fn_332_; 
v_fn_332_ = lean_ctor_get(v_fn_331_, 0);
if (lean_obj_tag(v_fn_332_) == 4)
{
lean_object* v_declName_333_; 
v_declName_333_ = lean_ctor_get(v_fn_332_, 0);
lean_inc(v_declName_333_);
if (lean_obj_tag(v_declName_333_) == 1)
{
lean_object* v_pre_334_; 
v_pre_334_ = lean_ctor_get(v_declName_333_, 0);
lean_inc(v_pre_334_);
if (lean_obj_tag(v_pre_334_) == 1)
{
lean_object* v_pre_335_; 
v_pre_335_ = lean_ctor_get(v_pre_334_, 0);
lean_inc(v_pre_335_);
if (lean_obj_tag(v_pre_335_) == 1)
{
lean_object* v_pre_336_; 
v_pre_336_ = lean_ctor_get(v_pre_335_, 0);
lean_inc(v_pre_336_);
if (lean_obj_tag(v_pre_336_) == 1)
{
lean_object* v_pre_337_; 
v_pre_337_ = lean_ctor_get(v_pre_336_, 0);
lean_inc(v_pre_337_);
if (lean_obj_tag(v_pre_337_) == 0)
{
lean_object* v_u_338_; lean_object* v_00_u03c3s_339_; lean_object* v_hyps_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_402_; 
v_u_338_ = lean_ctor_get(v_val_328_, 0);
v_00_u03c3s_339_ = lean_ctor_get(v_val_328_, 1);
v_hyps_340_ = lean_ctor_get(v_val_328_, 2);
v_isSharedCheck_402_ = !lean_is_exclusive(v_val_328_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; 
v_unused_403_ = lean_ctor_get(v_val_328_, 3);
lean_dec(v_unused_403_);
v___x_342_ = v_val_328_;
v_isShared_343_ = v_isSharedCheck_402_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_hyps_340_);
lean_inc(v_00_u03c3s_339_);
lean_inc(v_u_338_);
lean_dec(v_val_328_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_402_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v_arg_344_; lean_object* v_arg_345_; lean_object* v_arg_346_; lean_object* v_str_347_; lean_object* v_str_348_; lean_object* v_str_349_; lean_object* v_str_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_arg_344_ = lean_ctor_get(v_target_329_, 1);
lean_inc_ref(v_arg_344_);
lean_dec_ref_known(v_target_329_, 2);
v_arg_345_ = lean_ctor_get(v_fn_330_, 1);
lean_inc_ref(v_arg_345_);
lean_dec_ref_known(v_fn_330_, 2);
v_arg_346_ = lean_ctor_get(v_fn_331_, 1);
lean_inc_ref(v_arg_346_);
lean_dec_ref_known(v_fn_331_, 2);
v_str_347_ = lean_ctor_get(v_declName_333_, 1);
lean_inc_ref(v_str_347_);
lean_dec_ref_known(v_declName_333_, 2);
v_str_348_ = lean_ctor_get(v_pre_334_, 1);
lean_inc_ref(v_str_348_);
lean_dec_ref_known(v_pre_334_, 2);
v_str_349_ = lean_ctor_get(v_pre_335_, 1);
lean_inc_ref(v_str_349_);
lean_dec_ref_known(v_pre_335_, 2);
v_str_350_ = lean_ctor_get(v_pre_336_, 1);
lean_inc_ref(v_str_350_);
lean_dec_ref_known(v_pre_336_, 2);
v___x_351_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__2));
v___x_352_ = lean_string_dec_eq(v_str_350_, v___x_351_);
lean_dec_ref(v_str_350_);
if (v___x_352_ == 0)
{
lean_dec_ref(v_str_349_);
lean_dec_ref(v_str_348_);
lean_dec_ref(v_str_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_dec_ref(v_arg_344_);
lean_del_object(v___x_342_);
lean_dec_ref(v_hyps_340_);
lean_dec_ref(v_00_u03c3s_339_);
lean_dec(v_u_338_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
else
{
lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__3));
v___x_354_ = lean_string_dec_eq(v_str_349_, v___x_353_);
lean_dec_ref(v_str_349_);
if (v___x_354_ == 0)
{
lean_dec_ref(v_str_348_);
lean_dec_ref(v_str_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_dec_ref(v_arg_344_);
lean_del_object(v___x_342_);
lean_dec_ref(v_hyps_340_);
lean_dec_ref(v_00_u03c3s_339_);
lean_dec(v_u_338_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
else
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__4));
v___x_356_ = lean_string_dec_eq(v_str_348_, v___x_355_);
lean_dec_ref(v_str_348_);
if (v___x_356_ == 0)
{
lean_dec_ref(v_str_347_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_dec_ref(v_arg_344_);
lean_del_object(v___x_342_);
lean_dec_ref(v_hyps_340_);
lean_dec_ref(v_00_u03c3s_339_);
lean_dec(v_u_338_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
else
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__5));
v___x_358_ = lean_string_dec_eq(v_str_347_, v___x_357_);
lean_dec_ref(v_str_347_);
if (v___x_358_ == 0)
{
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_dec_ref(v_arg_344_);
lean_del_object(v___x_342_);
lean_dec_ref(v_hyps_340_);
lean_dec_ref(v_00_u03c3s_339_);
lean_dec(v_u_338_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
else
{
lean_object* v___x_360_; 
lean_inc_ref(v_arg_345_);
lean_inc_ref(v_hyps_340_);
lean_inc_ref(v_00_u03c3s_339_);
lean_inc(v_u_338_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 3, v_arg_345_);
v___x_360_ = v___x_342_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_u_338_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_00_u03c3s_339_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v_hyps_340_);
lean_ctor_set(v_reuseFailAlloc_401_, 3, v_arg_345_);
v___x_360_ = v_reuseFailAlloc_401_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_360_);
v___x_362_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_361_, v_pre_337_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
lean_inc_ref(v_arg_344_);
lean_inc_ref(v_hyps_340_);
lean_inc(v_u_338_);
v___x_364_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_364_, 0, v_u_338_);
lean_ctor_set(v___x_364_, 1, v_00_u03c3s_339_);
lean_ctor_set(v___x_364_, 2, v_hyps_340_);
lean_ctor_set(v___x_364_, 3, v_arg_344_);
v___x_365_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_364_);
v___x_366_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_365_, v_pre_337_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_383_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc_n(v_a_367_, 2);
lean_dec_ref_known(v___x_366_, 1);
v___x_368_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__7));
v___x_369_ = lean_box(0);
v___x_370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_370_, 0, v_u_338_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = l_Lean_mkConst(v___x_368_, v___x_370_);
lean_inc(v_a_363_);
v___x_372_ = l_Lean_mkApp6(v___x_371_, v_arg_346_, v_hyps_340_, v_arg_345_, v_arg_344_, v_a_363_, v_a_367_);
v___x_373_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvar_310_, v___x_372_, v_a_312_);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_383_ == 0)
{
lean_object* v_unused_384_; 
v_unused_384_ = lean_ctor_get(v___x_373_, 0);
lean_dec(v_unused_384_);
v___x_375_ = v___x_373_;
v_isShared_376_ = v_isSharedCheck_383_;
goto v_resetjp_374_;
}
else
{
lean_dec(v___x_373_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_383_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_377_ = l_Lean_Expr_mvarId_x21(v_a_363_);
lean_dec(v_a_363_);
v___x_378_ = l_Lean_Expr_mvarId_x21(v_a_367_);
lean_dec(v_a_367_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_379_);
v___x_381_ = v___x_375_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_a_363_);
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_hyps_340_);
lean_dec(v_u_338_);
lean_dec(v_mvar_310_);
v_a_385_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_366_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_366_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v_arg_346_);
lean_dec_ref(v_arg_345_);
lean_dec_ref(v_arg_344_);
lean_dec_ref(v_hyps_340_);
lean_dec_ref(v_00_u03c3s_339_);
lean_dec(v_u_338_);
lean_dec(v_mvar_310_);
v_a_393_ = lean_ctor_get(v___x_362_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_362_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_362_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_362_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
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
lean_dec_ref_known(v_pre_336_, 2);
lean_dec(v_pre_337_);
lean_dec_ref_known(v_pre_335_, 2);
lean_dec_ref_known(v_pre_334_, 2);
lean_dec_ref_known(v_declName_333_, 2);
lean_dec_ref_known(v_fn_331_, 2);
lean_dec_ref_known(v_fn_330_, 2);
lean_dec_ref_known(v_target_329_, 2);
lean_dec(v_val_328_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
}
else
{
lean_dec_ref_known(v_pre_335_, 2);
lean_dec(v_pre_336_);
lean_dec_ref_known(v_pre_334_, 2);
lean_dec_ref_known(v_declName_333_, 2);
lean_dec_ref_known(v_fn_331_, 2);
lean_dec_ref_known(v_fn_330_, 2);
lean_dec_ref_known(v_target_329_, 2);
lean_dec(v_val_328_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
}
else
{
lean_dec(v_pre_335_);
lean_dec_ref_known(v_pre_334_, 2);
lean_dec_ref_known(v_declName_333_, 2);
lean_dec_ref_known(v_fn_331_, 2);
lean_dec_ref_known(v_fn_330_, 2);
lean_dec_ref_known(v_target_329_, 2);
lean_dec(v_val_328_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
}
else
{
lean_dec_ref_known(v_declName_333_, 2);
lean_dec(v_pre_334_);
lean_dec_ref_known(v_fn_331_, 2);
lean_dec_ref_known(v_fn_330_, 2);
lean_dec_ref_known(v_target_329_, 2);
lean_dec(v_val_328_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
}
else
{
lean_dec(v_declName_333_);
lean_dec_ref_known(v_fn_331_, 2);
lean_dec_ref_known(v_fn_330_, 2);
lean_dec_ref_known(v_target_329_, 2);
lean_dec(v_val_328_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
}
else
{
lean_dec_ref_known(v_fn_331_, 2);
lean_dec_ref_known(v_fn_330_, 2);
lean_dec_ref_known(v_target_329_, 2);
lean_dec(v_val_328_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
}
else
{
lean_dec_ref(v_fn_331_);
lean_dec_ref_known(v_fn_330_, 2);
lean_dec_ref_known(v_target_329_, 2);
lean_dec(v_val_328_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
}
else
{
lean_dec_ref_known(v_target_329_, 2);
lean_dec_ref(v_fn_330_);
lean_dec(v_val_328_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
}
else
{
lean_dec_ref(v_target_329_);
lean_dec(v_val_328_);
lean_dec(v_mvar_310_);
v___y_317_ = v_a_311_;
v___y_318_ = v_a_312_;
v___y_319_ = v_a_313_;
v___y_320_ = v_a_314_;
goto v___jp_316_;
}
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v___x_327_);
lean_dec(v_mvar_310_);
v___x_404_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9, &l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__9);
v___x_405_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v___x_404_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
return v___x_405_;
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_dec(v_mvar_310_);
v_a_406_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_413_ == 0)
{
v___x_408_ = v___x_323_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_323_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
v___jp_316_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1, &l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___closed__1);
v___x_322_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v___x_321_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
return v___x_322_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvar_310_ = stack[0].m_obj;
lean_object* v_a_311_ = stack[1].m_obj;
lean_object* v_a_312_ = stack[2].m_obj;
lean_object* v_a_313_ = stack[3].m_obj;
lean_object* v_a_314_ = stack[4].m_obj;
lean_object* v_res_414_;
v_res_414_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(v_mvar_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_);
stack->m_obj
 = v_res_414_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore___boxed(lean_object* v_mvar_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(v_mvar_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_a_416_);
return v_res_421_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0(lean_object* v_00_u03b1_422_, lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___redArg(v_msg_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
return v___x_429_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_423_ = stack[1].m_obj;
lean_object* v___y_424_ = stack[2].m_obj;
lean_object* v___y_425_ = stack[3].m_obj;
lean_object* v___y_426_ = stack[4].m_obj;
lean_object* v___y_427_ = stack[5].m_obj;
lean_object* v_res_430_;
v_res_430_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0(lean_box(0), v_msg_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0___boxed(lean_object* v_00_u03b1_431_, lean_object* v_msg_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__0(v_00_u03b1_431_, v_msg_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_438_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2(lean_object* v_mvarId_439_, lean_object* v_val_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___redArg(v_mvarId_439_, v_val_440_, v___y_442_);
return v___x_446_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_439_ = stack[0].m_obj;
lean_object* v_val_440_ = stack[1].m_obj;
lean_object* v___y_441_ = stack[2].m_obj;
lean_object* v___y_442_ = stack[3].m_obj;
lean_object* v___y_443_ = stack[4].m_obj;
lean_object* v___y_444_ = stack[5].m_obj;
lean_object* v_res_447_;
v_res_447_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2(v_mvarId_439_, v_val_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2___boxed(lean_object* v_mvarId_448_, lean_object* v_val_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2(v_mvarId_448_, v_val_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3(lean_object* v_00_u03b2_456_, lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3___redArg(v_x_457_, v_x_458_, v_x_459_);
return v___x_460_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_461_, lean_object* v_x_462_, size_t v_x_463_, size_t v_x_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___redArg(v_x_462_, v_x_463_, v_x_464_, v_x_465_, v_x_466_);
return v___x_467_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_462_ = stack[1].m_obj;
size_t v_x_463_ = stack[2].m_num;
size_t v_x_464_ = stack[3].m_num;
lean_object* v_x_465_ = stack[4].m_obj;
lean_object* v_x_466_ = stack[5].m_obj;
lean_object* v_res_468_;
v_res_468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4(lean_box(0), v_x_462_, v_x_463_, v_x_464_, v_x_465_, v_x_466_);
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_469_, lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
size_t v_x_4454__boxed_475_; size_t v_x_4455__boxed_476_; lean_object* v_res_477_; 
v_x_4454__boxed_475_ = lean_unbox_usize(v_x_471_);
lean_dec(v_x_471_);
v_x_4455__boxed_476_ = lean_unbox_usize(v_x_472_);
lean_dec(v_x_472_);
v_res_477_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4(v_00_u03b2_469_, v_x_470_, v_x_4454__boxed_475_, v_x_4455__boxed_476_, v_x_473_, v_x_474_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_478_, lean_object* v_n_479_, lean_object* v_k_480_, lean_object* v_v_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5___redArg(v_n_479_, v_k_480_, v_v_481_);
return v___x_482_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_483_, size_t v_depth_484_, lean_object* v_keys_485_, lean_object* v_vals_486_, lean_object* v_heq_487_, lean_object* v_i_488_, lean_object* v_entries_489_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_484_, v_keys_485_, v_vals_486_, v_i_488_, v_entries_489_);
return v___x_490_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_484_ = stack[1].m_num;
lean_object* v_keys_485_ = stack[2].m_obj;
lean_object* v_vals_486_ = stack[3].m_obj;
lean_object* v_i_488_ = stack[5].m_obj;
lean_object* v_entries_489_ = stack[6].m_obj;
lean_object* v_res_491_;
v_res_491_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6(lean_box(0), v_depth_484_, v_keys_485_, v_vals_486_, lean_box(0), v_i_488_, v_entries_489_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_492_, lean_object* v_depth_493_, lean_object* v_keys_494_, lean_object* v_vals_495_, lean_object* v_heq_496_, lean_object* v_i_497_, lean_object* v_entries_498_){
_start:
{
size_t v_depth_boxed_499_; lean_object* v_res_500_; 
v_depth_boxed_499_ = lean_unbox_usize(v_depth_493_);
lean_dec(v_depth_493_);
v_res_500_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_492_, v_depth_boxed_499_, v_keys_494_, v_vals_495_, v_heq_496_, v_i_497_, v_entries_498_);
lean_dec_ref(v_vals_495_);
lean_dec_ref(v_keys_494_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_501_, lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_mConstructorCore_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_502_, v_x_503_, v_x_504_, v_x_505_);
return v___x_506_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0(lean_object* v_x_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; 
lean_inc(v___y_511_);
lean_inc_ref(v___y_510_);
lean_inc(v___y_509_);
lean_inc_ref(v___y_508_);
v___x_517_ = lean_apply_9(v_x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, lean_box(0));
return v___x_517_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_507_ = stack[0].m_obj;
lean_object* v___y_508_ = stack[1].m_obj;
lean_object* v___y_509_ = stack[2].m_obj;
lean_object* v___y_510_ = stack[3].m_obj;
lean_object* v___y_511_ = stack[4].m_obj;
lean_object* v___y_512_ = stack[5].m_obj;
lean_object* v___y_513_ = stack[6].m_obj;
lean_object* v___y_514_ = stack[7].m_obj;
lean_object* v___y_515_ = stack[8].m_obj;
lean_object* v_res_518_;
v_res_518_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0(v_x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0___boxed(lean_object* v_x_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0(v_x_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_529_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(lean_object* v_mvarId_530_, lean_object* v_x_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___f_541_; lean_object* v___x_542_; 
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
lean_inc(v___y_533_);
lean_inc_ref(v___y_532_);
v___f_541_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_541_, 0, v_x_531_);
lean_closure_set(v___f_541_, 1, v___y_532_);
lean_closure_set(v___f_541_, 2, v___y_533_);
lean_closure_set(v___f_541_, 3, v___y_534_);
lean_closure_set(v___f_541_, 4, v___y_535_);
v___x_542_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_530_, v___f_541_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
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
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_530_ = stack[0].m_obj;
lean_object* v_x_531_ = stack[1].m_obj;
lean_object* v___y_532_ = stack[2].m_obj;
lean_object* v___y_533_ = stack[3].m_obj;
lean_object* v___y_534_ = stack[4].m_obj;
lean_object* v___y_535_ = stack[5].m_obj;
lean_object* v___y_536_ = stack[6].m_obj;
lean_object* v___y_537_ = stack[7].m_obj;
lean_object* v___y_538_ = stack[8].m_obj;
lean_object* v___y_539_ = stack[9].m_obj;
lean_object* v_res_551_;
v_res_551_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_mvarId_530_, v_x_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
stack->m_obj
 = v_res_551_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg___boxed(lean_object* v_mvarId_552_, lean_object* v_x_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_mvarId_552_, v_x_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_563_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0(lean_object* v_00_u03b1_564_, lean_object* v_mvarId_565_, lean_object* v_x_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_mvarId_565_, v_x_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
return v___x_576_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_565_ = stack[1].m_obj;
lean_object* v_x_566_ = stack[2].m_obj;
lean_object* v___y_567_ = stack[3].m_obj;
lean_object* v___y_568_ = stack[4].m_obj;
lean_object* v___y_569_ = stack[5].m_obj;
lean_object* v___y_570_ = stack[6].m_obj;
lean_object* v___y_571_ = stack[7].m_obj;
lean_object* v___y_572_ = stack[8].m_obj;
lean_object* v___y_573_ = stack[9].m_obj;
lean_object* v___y_574_ = stack[10].m_obj;
lean_object* v_res_577_;
v_res_577_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0(lean_box(0), v_mvarId_565_, v_x_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
stack->m_obj
 = v_res_577_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___boxed(lean_object* v_00_u03b1_578_, lean_object* v_mvarId_579_, lean_object* v_x_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0(v_00_u03b1_578_, v_mvarId_579_, v_x_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
return v_res_590_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0(lean_object* v_a_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Elab_Tactic_Do_ProofMode_mConstructorCore(v_a_591_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v_fst_603_; lean_object* v_snd_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_614_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v_fst_603_ = lean_ctor_get(v_a_602_, 0);
v_snd_604_ = lean_ctor_get(v_a_602_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_a_602_);
if (v_isSharedCheck_614_ == 0)
{
v___x_606_ = v_a_602_;
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_snd_604_);
lean_inc(v_fst_603_);
lean_dec(v_a_602_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_608_ = lean_box(0);
if (v_isShared_607_ == 0)
{
lean_ctor_set_tag(v___x_606_, 1);
lean_ctor_set(v___x_606_, 1, v___x_608_);
lean_ctor_set(v___x_606_, 0, v_snd_604_);
v___x_610_ = v___x_606_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_snd_604_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_608_);
v___x_610_ = v_reuseFailAlloc_613_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_611_, 0, v_fst_603_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_611_, v___y_593_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
return v___x_612_;
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
v_a_615_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_601_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_601_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_591_ = stack[0].m_obj;
lean_object* v___y_592_ = stack[1].m_obj;
lean_object* v___y_593_ = stack[2].m_obj;
lean_object* v___y_594_ = stack[3].m_obj;
lean_object* v___y_595_ = stack[4].m_obj;
lean_object* v___y_596_ = stack[5].m_obj;
lean_object* v___y_597_ = stack[6].m_obj;
lean_object* v___y_598_ = stack[7].m_obj;
lean_object* v___y_599_ = stack[8].m_obj;
lean_object* v_res_623_;
v_res_623_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0(v_a_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
stack->m_obj
 = v_res_623_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0___boxed(lean_object* v_a_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0(v_a_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
return v_res_634_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_636_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___f_646_; lean_object* v___x_647_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc_n(v_a_645_, 2);
lean_dec_ref_known(v___x_644_, 1);
v___f_646_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_646_, 0, v_a_645_);
v___x_647_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_spec__0___redArg(v_a_645_, v___f_646_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
return v___x_647_;
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
v_a_648_ = lean_ctor_get(v___x_644_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_644_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_644_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_635_ = stack[0].m_obj;
lean_object* v_a_636_ = stack[1].m_obj;
lean_object* v_a_637_ = stack[2].m_obj;
lean_object* v_a_638_ = stack[3].m_obj;
lean_object* v_a_639_ = stack[4].m_obj;
lean_object* v_a_640_ = stack[5].m_obj;
lean_object* v_a_641_ = stack[6].m_obj;
lean_object* v_a_642_ = stack[7].m_obj;
lean_object* v_res_656_;
v_res_656_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
stack->m_obj
 = v_res_656_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg___boxed(lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
lean_dec(v_a_664_);
lean_dec_ref(v_a_663_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
lean_dec(v_a_658_);
lean_dec_ref(v_a_657_);
return v_res_666_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor(lean_object* v_x_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___redArg(v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
return v___x_677_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_667_ = stack[0].m_obj;
lean_object* v_a_668_ = stack[1].m_obj;
lean_object* v_a_669_ = stack[2].m_obj;
lean_object* v_a_670_ = stack[3].m_obj;
lean_object* v_a_671_ = stack[4].m_obj;
lean_object* v_a_672_ = stack[5].m_obj;
lean_object* v_a_673_ = stack[6].m_obj;
lean_object* v_a_674_ = stack[7].m_obj;
lean_object* v_a_675_ = stack[8].m_obj;
lean_object* v_res_678_;
v_res_678_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor(v_x_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_);
stack->m_obj
 = v_res_678_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___boxed(lean_object* v_x_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor(v_x_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
lean_dec(v_a_687_);
lean_dec_ref(v_a_686_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_x_679_);
return v_res_689_;
}
}
lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1(){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_710_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_711_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__4));
v___x_712_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___closed__8));
v___x_713_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___boxed), 10, 0);
v___x_714_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_710_, v___x_711_, v___x_712_, v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_715_;
v_res_715_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1();
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1___boxed(lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1();
return v_res_717_;
}
}
lean_object* runtime_initialize_Std_Tactic_Do_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_MGoal(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Constructor(uint8_t builtin) {
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
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Constructor_0__Lean_Elab_Tactic_Do_ProofMode_elabMConstructor___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMConstructor__1();
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
