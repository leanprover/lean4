// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Exfalso
// Imports: public import Lean.Elab.Tactic.Do.ProofMode.Basic
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "exfalso"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(115, 125, 65, 225, 236, 72, 188, 25)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not in proof mode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mexfalso"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 221, 191, 226, 253, 105, 73, 187)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabMExfalso"};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(148, 175, 96, 100, 84, 165, 55, 147)}};
static const lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___boxed(lean_object*);
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__1));
v___x_6_ = l_Lean_mkConst(v___x_5_, v___x_4_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp(lean_object* v_u_7_, lean_object* v_00_u03c3s_8_){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2, &l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp___closed__2);
v___x_10_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkPure(v_u_7_, v_00_u03c3s_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg(lean_object* v_e_11_, lean_object* v___y_12_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = l_Lean_Expr_hasMVar(v_e_11_);
if (v___x_14_ == 0)
{
lean_object* v___x_15_; 
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v_e_11_);
return v___x_15_;
}
else
{
lean_object* v___x_16_; lean_object* v_mctx_17_; lean_object* v___x_18_; lean_object* v_fst_19_; lean_object* v_snd_20_; lean_object* v___x_21_; lean_object* v_cache_22_; lean_object* v_zetaDeltaFVarIds_23_; lean_object* v_postponed_24_; lean_object* v_diag_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_34_; 
v___x_16_ = lean_st_ref_get(v___y_12_);
v_mctx_17_ = lean_ctor_get(v___x_16_, 0);
lean_inc_ref(v_mctx_17_);
lean_dec(v___x_16_);
v___x_18_ = l_Lean_instantiateMVarsCore(v_mctx_17_, v_e_11_);
v_fst_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_fst_19_);
v_snd_20_ = lean_ctor_get(v___x_18_, 1);
lean_inc(v_snd_20_);
lean_dec_ref(v___x_18_);
v___x_21_ = lean_st_ref_take(v___y_12_);
v_cache_22_ = lean_ctor_get(v___x_21_, 1);
v_zetaDeltaFVarIds_23_ = lean_ctor_get(v___x_21_, 2);
v_postponed_24_ = lean_ctor_get(v___x_21_, 3);
v_diag_25_ = lean_ctor_get(v___x_21_, 4);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_34_ == 0)
{
lean_object* v_unused_35_; 
v_unused_35_ = lean_ctor_get(v___x_21_, 0);
lean_dec(v_unused_35_);
v___x_27_ = v___x_21_;
v_isShared_28_ = v_isSharedCheck_34_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_diag_25_);
lean_inc(v_postponed_24_);
lean_inc(v_zetaDeltaFVarIds_23_);
lean_inc(v_cache_22_);
lean_dec(v___x_21_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_34_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v_snd_20_);
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v_snd_20_);
lean_ctor_set(v_reuseFailAlloc_33_, 1, v_cache_22_);
lean_ctor_set(v_reuseFailAlloc_33_, 2, v_zetaDeltaFVarIds_23_);
lean_ctor_set(v_reuseFailAlloc_33_, 3, v_postponed_24_);
lean_ctor_set(v_reuseFailAlloc_33_, 4, v_diag_25_);
v___x_30_ = v_reuseFailAlloc_33_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_st_ref_set(v___y_12_, v___x_30_);
v___x_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_32_, 0, v_fst_19_);
return v___x_32_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg___boxed(lean_object* v_e_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg(v_e_36_, v___y_37_);
lean_dec(v___y_37_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0(lean_object* v_e_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg(v_e_40_, v___y_46_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___boxed(lean_object* v_e_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0(v_e_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___lam__0(lean_object* v_x_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; 
lean_inc(v___y_66_);
lean_inc_ref(v___y_65_);
lean_inc(v___y_64_);
lean_inc_ref(v___y_63_);
v___x_72_ = lean_apply_9(v_x_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, lean_box(0));
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___lam__0___boxed(lean_object* v_x_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___lam__0(v_x_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg(lean_object* v_mvarId_84_, lean_object* v_x_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___f_95_; lean_object* v___x_96_; 
lean_inc(v___y_89_);
lean_inc_ref(v___y_88_);
lean_inc(v___y_87_);
lean_inc_ref(v___y_86_);
v___f_95_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_95_, 0, v_x_85_);
lean_closure_set(v___f_95_, 1, v___y_86_);
lean_closure_set(v___f_95_, 2, v___y_87_);
lean_closure_set(v___f_95_, 3, v___y_88_);
lean_closure_set(v___f_95_, 4, v___y_89_);
v___x_96_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_84_, v___f_95_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
if (lean_obj_tag(v___x_96_) == 0)
{
return v___x_96_;
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg___boxed(lean_object* v_mvarId_105_, lean_object* v_x_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg(v_mvarId_105_, v_x_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3(lean_object* v_00_u03b1_117_, lean_object* v_mvarId_118_, lean_object* v_x_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg(v_mvarId_118_, v_x_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___boxed(lean_object* v_00_u03b1_130_, lean_object* v_mvarId_131_, lean_object* v_x_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3(v_00_u03b1_130_, v_mvarId_131_, v_x_132_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v___y_134_);
lean_dec_ref(v___y_133_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3(lean_object* v_msgData_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; lean_object* v_env_150_; lean_object* v___x_151_; lean_object* v_mctx_152_; lean_object* v_lctx_153_; lean_object* v_options_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_149_ = lean_st_ref_get(v___y_147_);
v_env_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc_ref(v_env_150_);
lean_dec(v___x_149_);
v___x_151_ = lean_st_ref_get(v___y_145_);
v_mctx_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc_ref(v_mctx_152_);
lean_dec(v___x_151_);
v_lctx_153_ = lean_ctor_get(v___y_144_, 2);
v_options_154_ = lean_ctor_get(v___y_146_, 2);
lean_inc_ref(v_options_154_);
lean_inc_ref(v_lctx_153_);
v___x_155_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_155_, 0, v_env_150_);
lean_ctor_set(v___x_155_, 1, v_mctx_152_);
lean_ctor_set(v___x_155_, 2, v_lctx_153_);
lean_ctor_set(v___x_155_, 3, v_options_154_);
v___x_156_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v_msgData_143_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3___boxed(lean_object* v_msgData_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3(v_msgData_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(lean_object* v_msg_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_ref_171_; lean_object* v___x_172_; lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_181_; 
v_ref_171_ = lean_ctor_get(v___y_168_, 5);
v___x_172_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3(v_msg_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_181_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_181_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
lean_inc(v_ref_171_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_ref_171_);
lean_ctor_set(v___x_177_, 1, v_a_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set_tag(v___x_175_, 1);
lean_ctor_set(v___x_175_, 0, v___x_177_);
v___x_179_ = v___x_175_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg___boxed(lean_object* v_msg_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(v_msg_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
lean_object* v_ks_193_; lean_object* v_vs_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_218_; 
v_ks_193_ = lean_ctor_get(v_x_189_, 0);
v_vs_194_ = lean_ctor_get(v_x_189_, 1);
v_isSharedCheck_218_ = !lean_is_exclusive(v_x_189_);
if (v_isSharedCheck_218_ == 0)
{
v___x_196_ = v_x_189_;
v_isShared_197_ = v_isSharedCheck_218_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_vs_194_);
lean_inc(v_ks_193_);
lean_dec(v_x_189_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_218_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_198_ = lean_array_get_size(v_ks_193_);
v___x_199_ = lean_nat_dec_lt(v_x_190_, v___x_198_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
lean_dec(v_x_190_);
v___x_200_ = lean_array_push(v_ks_193_, v_x_191_);
v___x_201_ = lean_array_push(v_vs_194_, v_x_192_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v___x_201_);
lean_ctor_set(v___x_196_, 0, v___x_200_);
v___x_203_ = v___x_196_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_200_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
else
{
lean_object* v_k_x27_205_; uint8_t v___x_206_; 
v_k_x27_205_ = lean_array_fget_borrowed(v_ks_193_, v_x_190_);
v___x_206_ = l_Lean_instBEqMVarId_beq(v_x_191_, v_k_x27_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_208_; 
if (v_isShared_197_ == 0)
{
v___x_208_ = v___x_196_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_ks_193_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_vs_194_);
v___x_208_ = v_reuseFailAlloc_212_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_add(v_x_190_, v___x_209_);
lean_dec(v_x_190_);
v_x_189_ = v___x_208_;
v_x_190_ = v___x_210_;
goto _start;
}
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_213_ = lean_array_fset(v_ks_193_, v_x_190_, v_x_191_);
v___x_214_ = lean_array_fset(v_vs_194_, v_x_190_, v_x_192_);
lean_dec(v_x_190_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v___x_214_);
lean_ctor_set(v___x_196_, 0, v___x_213_);
v___x_216_ = v___x_196_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_213_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_219_, lean_object* v_k_220_, lean_object* v_v_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_219_, v___x_222_, v_k_220_, v_v_221_);
return v___x_223_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_224_; size_t v___x_225_; size_t v___x_226_; 
v___x_224_ = ((size_t)5ULL);
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_shift_left(v___x_225_, v___x_224_);
return v___x_226_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_227_; size_t v___x_228_; size_t v___x_229_; 
v___x_227_ = ((size_t)1ULL);
v___x_228_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_229_ = lean_usize_sub(v___x_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(lean_object* v_x_231_, size_t v_x_232_, size_t v_x_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_object* v_es_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; lean_object* v_j_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_es_236_ = lean_ctor_get(v_x_231_, 0);
v___x_237_ = ((size_t)5ULL);
v___x_238_ = ((size_t)1ULL);
v___x_239_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__1);
v___x_240_ = lean_usize_land(v_x_232_, v___x_239_);
v_j_241_ = lean_usize_to_nat(v___x_240_);
v___x_242_ = lean_array_get_size(v_es_236_);
v___x_243_ = lean_nat_dec_lt(v_j_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_dec(v_j_241_);
lean_dec(v_x_235_);
lean_dec(v_x_234_);
return v_x_231_;
}
else
{
lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_280_; 
lean_inc_ref(v_es_236_);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v_x_231_, 0);
lean_dec(v_unused_281_);
v___x_245_ = v_x_231_;
v_isShared_246_ = v_isSharedCheck_280_;
goto v_resetjp_244_;
}
else
{
lean_dec(v_x_231_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_280_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v_v_247_; lean_object* v___x_248_; lean_object* v_xs_x27_249_; lean_object* v___y_251_; 
v_v_247_ = lean_array_fget(v_es_236_, v_j_241_);
v___x_248_ = lean_box(0);
v_xs_x27_249_ = lean_array_fset(v_es_236_, v_j_241_, v___x_248_);
switch(lean_obj_tag(v_v_247_))
{
case 0:
{
lean_object* v_key_256_; lean_object* v_val_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_267_; 
v_key_256_ = lean_ctor_get(v_v_247_, 0);
v_val_257_ = lean_ctor_get(v_v_247_, 1);
v_isSharedCheck_267_ = !lean_is_exclusive(v_v_247_);
if (v_isSharedCheck_267_ == 0)
{
v___x_259_ = v_v_247_;
v_isShared_260_ = v_isSharedCheck_267_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_val_257_);
lean_inc(v_key_256_);
lean_dec(v_v_247_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_267_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
uint8_t v___x_261_; 
v___x_261_ = l_Lean_instBEqMVarId_beq(v_x_234_, v_key_256_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; lean_object* v___x_263_; 
lean_del_object(v___x_259_);
v___x_262_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_256_, v_val_257_, v_x_234_, v_x_235_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
v___y_251_ = v___x_263_;
goto v___jp_250_;
}
else
{
lean_object* v___x_265_; 
lean_dec(v_val_257_);
lean_dec(v_key_256_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v_x_235_);
lean_ctor_set(v___x_259_, 0, v_x_234_);
v___x_265_ = v___x_259_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_x_234_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_x_235_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
v___y_251_ = v___x_265_;
goto v___jp_250_;
}
}
}
}
case 1:
{
lean_object* v_node_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_278_; 
v_node_268_ = lean_ctor_get(v_v_247_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_v_247_);
if (v_isSharedCheck_278_ == 0)
{
v___x_270_ = v_v_247_;
v_isShared_271_ = v_isSharedCheck_278_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_node_268_);
lean_dec(v_v_247_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_278_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_272_ = lean_usize_shift_right(v_x_232_, v___x_237_);
v___x_273_ = lean_usize_add(v_x_233_, v___x_238_);
v___x_274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_node_268_, v___x_272_, v___x_273_, v_x_234_, v_x_235_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_274_);
v___x_276_ = v___x_270_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
v___y_251_ = v___x_276_;
goto v___jp_250_;
}
}
}
default: 
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_x_234_);
lean_ctor_set(v___x_279_, 1, v_x_235_);
v___y_251_ = v___x_279_;
goto v___jp_250_;
}
}
v___jp_250_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = lean_array_fset(v_xs_x27_249_, v_j_241_, v___y_251_);
lean_dec(v_j_241_);
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v___x_252_);
v___x_254_ = v___x_245_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
else
{
lean_object* v_ks_282_; lean_object* v_vs_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_303_; 
v_ks_282_ = lean_ctor_get(v_x_231_, 0);
v_vs_283_ = lean_ctor_get(v_x_231_, 1);
v_isSharedCheck_303_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_303_ == 0)
{
v___x_285_ = v_x_231_;
v_isShared_286_ = v_isSharedCheck_303_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_vs_283_);
lean_inc(v_ks_282_);
lean_dec(v_x_231_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_303_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_ks_282_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_vs_283_);
v___x_288_ = v_reuseFailAlloc_302_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v_newNode_289_; uint8_t v___y_291_; size_t v___x_297_; uint8_t v___x_298_; 
v_newNode_289_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(v___x_288_, v_x_234_, v_x_235_);
v___x_297_ = ((size_t)7ULL);
v___x_298_ = lean_usize_dec_le(v___x_297_, v_x_233_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_299_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_289_);
v___x_300_ = lean_unsigned_to_nat(4u);
v___x_301_ = lean_nat_dec_lt(v___x_299_, v___x_300_);
lean_dec(v___x_299_);
v___y_291_ = v___x_301_;
goto v___jp_290_;
}
else
{
v___y_291_ = v___x_298_;
goto v___jp_290_;
}
v___jp_290_:
{
if (v___y_291_ == 0)
{
lean_object* v_ks_292_; lean_object* v_vs_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_ks_292_ = lean_ctor_get(v_newNode_289_, 0);
lean_inc_ref(v_ks_292_);
v_vs_293_ = lean_ctor_get(v_newNode_289_, 1);
lean_inc_ref(v_vs_293_);
lean_dec_ref(v_newNode_289_);
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__2);
v___x_296_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_x_233_, v_ks_292_, v_vs_293_, v___x_294_, v___x_295_);
lean_dec_ref(v_vs_293_);
lean_dec_ref(v_ks_292_);
return v___x_296_;
}
else
{
return v_newNode_289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_304_, lean_object* v_keys_305_, lean_object* v_vals_306_, lean_object* v_i_307_, lean_object* v_entries_308_){
_start:
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_array_get_size(v_keys_305_);
v___x_310_ = lean_nat_dec_lt(v_i_307_, v___x_309_);
if (v___x_310_ == 0)
{
lean_dec(v_i_307_);
return v_entries_308_;
}
else
{
lean_object* v_k_311_; lean_object* v_v_312_; uint64_t v___x_313_; size_t v_h_314_; size_t v___x_315_; lean_object* v___x_316_; size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; size_t v_h_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v_k_311_ = lean_array_fget_borrowed(v_keys_305_, v_i_307_);
v_v_312_ = lean_array_fget_borrowed(v_vals_306_, v_i_307_);
v___x_313_ = l_Lean_instHashableMVarId_hash(v_k_311_);
v_h_314_ = lean_uint64_to_usize(v___x_313_);
v___x_315_ = ((size_t)5ULL);
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = ((size_t)1ULL);
v___x_318_ = lean_usize_sub(v_depth_304_, v___x_317_);
v___x_319_ = lean_usize_mul(v___x_315_, v___x_318_);
v_h_320_ = lean_usize_shift_right(v_h_314_, v___x_319_);
v___x_321_ = lean_nat_add(v_i_307_, v___x_316_);
lean_dec(v_i_307_);
lean_inc(v_v_312_);
lean_inc(v_k_311_);
v___x_322_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_entries_308_, v_h_320_, v_depth_304_, v_k_311_, v_v_312_);
v_i_307_ = v___x_321_;
v_entries_308_ = v___x_322_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_324_, lean_object* v_keys_325_, lean_object* v_vals_326_, lean_object* v_i_327_, lean_object* v_entries_328_){
_start:
{
size_t v_depth_boxed_329_; lean_object* v_res_330_; 
v_depth_boxed_329_ = lean_unbox_usize(v_depth_324_);
lean_dec(v_depth_324_);
v_res_330_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_329_, v_keys_325_, v_vals_326_, v_i_327_, v_entries_328_);
lean_dec_ref(v_vals_326_);
lean_dec_ref(v_keys_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
size_t v_x_5675__boxed_336_; size_t v_x_5676__boxed_337_; lean_object* v_res_338_; 
v_x_5675__boxed_336_ = lean_unbox_usize(v_x_332_);
lean_dec(v_x_332_);
v_x_5676__boxed_337_ = lean_unbox_usize(v_x_333_);
lean_dec(v_x_333_);
v_res_338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_331_, v_x_5675__boxed_336_, v_x_5676__boxed_337_, v_x_334_, v_x_335_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
uint64_t v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_342_ = l_Lean_instHashableMVarId_hash(v_x_340_);
v___x_343_ = lean_uint64_to_usize(v___x_342_);
v___x_344_ = ((size_t)1ULL);
v___x_345_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_339_, v___x_343_, v___x_344_, v_x_340_, v_x_341_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(lean_object* v_mvarId_346_, lean_object* v_val_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; lean_object* v_mctx_351_; lean_object* v_cache_352_; lean_object* v_zetaDeltaFVarIds_353_; lean_object* v_postponed_354_; lean_object* v_diag_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_382_; 
v___x_350_ = lean_st_ref_take(v___y_348_);
v_mctx_351_ = lean_ctor_get(v___x_350_, 0);
v_cache_352_ = lean_ctor_get(v___x_350_, 1);
v_zetaDeltaFVarIds_353_ = lean_ctor_get(v___x_350_, 2);
v_postponed_354_ = lean_ctor_get(v___x_350_, 3);
v_diag_355_ = lean_ctor_get(v___x_350_, 4);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_382_ == 0)
{
v___x_357_ = v___x_350_;
v_isShared_358_ = v_isSharedCheck_382_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_diag_355_);
lean_inc(v_postponed_354_);
lean_inc(v_zetaDeltaFVarIds_353_);
lean_inc(v_cache_352_);
lean_inc(v_mctx_351_);
lean_dec(v___x_350_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_382_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v_depth_359_; lean_object* v_levelAssignDepth_360_; lean_object* v_mvarCounter_361_; lean_object* v_lDepth_362_; lean_object* v_decls_363_; lean_object* v_userNames_364_; lean_object* v_lAssignment_365_; lean_object* v_eAssignment_366_; lean_object* v_dAssignment_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_381_; 
v_depth_359_ = lean_ctor_get(v_mctx_351_, 0);
v_levelAssignDepth_360_ = lean_ctor_get(v_mctx_351_, 1);
v_mvarCounter_361_ = lean_ctor_get(v_mctx_351_, 2);
v_lDepth_362_ = lean_ctor_get(v_mctx_351_, 3);
v_decls_363_ = lean_ctor_get(v_mctx_351_, 4);
v_userNames_364_ = lean_ctor_get(v_mctx_351_, 5);
v_lAssignment_365_ = lean_ctor_get(v_mctx_351_, 6);
v_eAssignment_366_ = lean_ctor_get(v_mctx_351_, 7);
v_dAssignment_367_ = lean_ctor_get(v_mctx_351_, 8);
v_isSharedCheck_381_ = !lean_is_exclusive(v_mctx_351_);
if (v_isSharedCheck_381_ == 0)
{
v___x_369_ = v_mctx_351_;
v_isShared_370_ = v_isSharedCheck_381_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_dAssignment_367_);
lean_inc(v_eAssignment_366_);
lean_inc(v_lAssignment_365_);
lean_inc(v_userNames_364_);
lean_inc(v_decls_363_);
lean_inc(v_lDepth_362_);
lean_inc(v_mvarCounter_361_);
lean_inc(v_levelAssignDepth_360_);
lean_inc(v_depth_359_);
lean_dec(v_mctx_351_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_381_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(v_eAssignment_366_, v_mvarId_346_, v_val_347_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 7, v___x_371_);
v___x_373_ = v___x_369_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_depth_359_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_levelAssignDepth_360_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_mvarCounter_361_);
lean_ctor_set(v_reuseFailAlloc_380_, 3, v_lDepth_362_);
lean_ctor_set(v_reuseFailAlloc_380_, 4, v_decls_363_);
lean_ctor_set(v_reuseFailAlloc_380_, 5, v_userNames_364_);
lean_ctor_set(v_reuseFailAlloc_380_, 6, v_lAssignment_365_);
lean_ctor_set(v_reuseFailAlloc_380_, 7, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_380_, 8, v_dAssignment_367_);
v___x_373_ = v_reuseFailAlloc_380_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_375_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_373_);
v___x_375_ = v___x_357_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_cache_352_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_zetaDeltaFVarIds_353_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v_postponed_354_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v_diag_355_);
v___x_375_ = v_reuseFailAlloc_379_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_st_ref_set(v___y_348_, v___x_375_);
v___x_377_ = lean_box(0);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg___boxed(lean_object* v_mvarId_383_, lean_object* v_val_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(v_mvarId_383_, v_val_384_, v___y_385_);
lean_dec(v___y_385_);
return v_res_387_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__5));
v___x_399_ = l_Lean_stringToMessageData(v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0(lean_object* v_a_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; 
lean_inc(v_a_400_);
v___x_410_ = l_Lean_MVarId_getType(v_a_400_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_410_) == 0)
{
lean_object* v_a_411_; lean_object* v___x_412_; lean_object* v_a_413_; lean_object* v___x_414_; 
v_a_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_a_411_);
lean_dec_ref(v___x_410_);
v___x_412_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg(v_a_411_, v___y_406_);
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref(v___x_412_);
v___x_414_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_413_);
lean_dec(v_a_413_);
if (lean_obj_tag(v___x_414_) == 1)
{
lean_object* v_val_415_; lean_object* v_u_416_; lean_object* v_00_u03c3s_417_; lean_object* v_hyps_418_; lean_object* v_target_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_448_; 
v_val_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_val_415_);
lean_dec_ref(v___x_414_);
v_u_416_ = lean_ctor_get(v_val_415_, 0);
v_00_u03c3s_417_ = lean_ctor_get(v_val_415_, 1);
v_hyps_418_ = lean_ctor_get(v_val_415_, 2);
v_target_419_ = lean_ctor_get(v_val_415_, 3);
v_isSharedCheck_448_ = !lean_is_exclusive(v_val_415_);
if (v_isSharedCheck_448_ == 0)
{
v___x_421_ = v_val_415_;
v_isShared_422_ = v_isSharedCheck_448_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_target_419_);
lean_inc(v_hyps_418_);
lean_inc(v_00_u03c3s_417_);
lean_inc(v_u_416_);
lean_dec(v_val_415_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_448_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
lean_inc_ref_n(v_00_u03c3s_417_, 2);
lean_inc_n(v_u_416_, 2);
v___x_423_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp(v_u_416_, v_00_u03c3s_417_);
lean_inc_ref(v_hyps_418_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 3, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_u_416_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_00_u03c3s_417_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_hyps_418_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v___x_423_);
v___x_425_ = v_reuseFailAlloc_447_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_425_);
v___x_427_ = lean_box(0);
v___x_428_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_426_, v___x_427_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_n(v_a_429_, 2);
lean_dec_ref(v___x_428_);
v___x_430_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4));
v___x_431_ = lean_box(0);
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v_u_416_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v___x_433_ = l_Lean_mkConst(v___x_430_, v___x_432_);
v___x_434_ = l_Lean_mkApp4(v___x_433_, v_00_u03c3s_417_, v_hyps_418_, v_target_419_, v_a_429_);
v___x_435_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(v_a_400_, v___x_434_, v___y_406_);
lean_dec_ref(v___x_435_);
v___x_436_ = l_Lean_Expr_mvarId_x21(v_a_429_);
lean_dec(v_a_429_);
v___x_437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
lean_ctor_set(v___x_437_, 1, v___x_431_);
v___x_438_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_437_, v___y_402_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
return v___x_438_;
}
else
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
lean_dec_ref(v_target_419_);
lean_dec_ref(v_hyps_418_);
lean_dec_ref(v_00_u03c3s_417_);
lean_dec(v_u_416_);
lean_dec(v_a_400_);
v_a_439_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_446_ == 0)
{
v___x_441_ = v___x_428_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_428_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_439_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
}
else
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec(v___x_414_);
lean_dec(v_a_400_);
v___x_449_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6);
v___x_450_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(v___x_449_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
return v___x_450_;
}
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_458_; 
lean_dec(v_a_400_);
v_a_451_ = lean_ctor_get(v___x_410_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_458_ == 0)
{
v___x_453_ = v___x_410_;
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_410_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_458_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_451_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___boxed(lean_object* v_a_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0(v_a_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_471_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
if (lean_obj_tag(v___x_479_) == 0)
{
lean_object* v_a_480_; lean_object* v___f_481_; lean_object* v___x_482_; 
v_a_480_ = lean_ctor_get(v___x_479_, 0);
lean_inc_n(v_a_480_, 2);
lean_dec_ref(v___x_479_);
v___f_481_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_481_, 0, v_a_480_);
v___x_482_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg(v_a_480_, v___f_481_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
return v___x_482_;
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_a_483_ = lean_ctor_get(v___x_479_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_479_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_479_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_479_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___boxed(lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso(lean_object* v_x_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(v_a_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___boxed(lean_object* v_x_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso(v_x_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec(v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_x_512_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1(lean_object* v_mvarId_523_, lean_object* v_val_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(v_mvarId_523_, v_val_524_, v___y_530_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___boxed(lean_object* v_mvarId_535_, lean_object* v_val_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1(v_mvarId_535_, v_val_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2(lean_object* v_00_u03b1_547_, lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(v_msg_548_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___boxed(lean_object* v_00_u03b1_559_, lean_object* v_msg_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2(v_00_u03b1_559_, v_msg_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1(lean_object* v_00_u03b2_571_, lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(v_x_572_, v_x_573_, v_x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_576_, lean_object* v_x_577_, size_t v_x_578_, size_t v_x_579_, lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_577_, v_x_578_, v_x_579_, v_x_580_, v_x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_583_, lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
size_t v_x_6155__boxed_589_; size_t v_x_6156__boxed_590_; lean_object* v_res_591_; 
v_x_6155__boxed_589_ = lean_unbox_usize(v_x_585_);
lean_dec(v_x_585_);
v_x_6156__boxed_590_ = lean_unbox_usize(v_x_586_);
lean_dec(v_x_586_);
v_res_591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3(v_00_u03b2_583_, v_x_584_, v_x_6155__boxed_589_, v_x_6156__boxed_590_, v_x_587_, v_x_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_592_, lean_object* v_n_593_, lean_object* v_k_594_, lean_object* v_v_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(v_n_593_, v_k_594_, v_v_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_597_, size_t v_depth_598_, lean_object* v_keys_599_, lean_object* v_vals_600_, lean_object* v_heq_601_, lean_object* v_i_602_, lean_object* v_entries_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_598_, v_keys_599_, v_vals_600_, v_i_602_, v_entries_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_605_, lean_object* v_depth_606_, lean_object* v_keys_607_, lean_object* v_vals_608_, lean_object* v_heq_609_, lean_object* v_i_610_, lean_object* v_entries_611_){
_start:
{
size_t v_depth_boxed_612_; lean_object* v_res_613_; 
v_depth_boxed_612_ = lean_unbox_usize(v_depth_606_);
lean_dec(v_depth_606_);
v_res_613_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_605_, v_depth_boxed_612_, v_keys_607_, v_vals_608_, v_heq_609_, v_i_610_, v_entries_611_);
lean_dec_ref(v_vals_608_);
lean_dec_ref(v_keys_607_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_615_, v_x_616_, v_x_617_, v_x_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1(){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_640_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_641_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4));
v___x_642_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8));
v___x_643_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___boxed), 10, 0);
v___x_644_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_640_, v___x_641_, v___x_642_, v___x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___boxed(lean_object* v_a_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1();
return v_res_646_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(builtin);
}
#ifdef __cplusplus
}
#endif
