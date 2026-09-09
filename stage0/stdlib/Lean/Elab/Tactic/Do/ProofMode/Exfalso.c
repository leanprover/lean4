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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0;
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mexfalso"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 221, 191, 226, 253, 105, 73, 187)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ProofMode"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elabMExfalso"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 74, 68, 148, 0, 14, 81, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(148, 175, 96, 100, 84, 165, 55, 147)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___boxed(lean_object*);
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
v___x_31_ = lean_st_ref_put(v___y_12_, v___x_30_);
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
lean_object* v___x_149_; lean_object* v_env_150_; lean_object* v___x_151_; lean_object* v_toCold_152_; lean_object* v_mctx_153_; lean_object* v_lctx_154_; lean_object* v_options_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_149_ = lean_st_ref_get(v___y_147_);
v_env_150_ = lean_ctor_get(v___x_149_, 0);
lean_inc_ref(v_env_150_);
lean_dec(v___x_149_);
v___x_151_ = lean_st_ref_get(v___y_145_);
v_toCold_152_ = lean_ctor_get(v___y_146_, 0);
v_mctx_153_ = lean_ctor_get(v___x_151_, 0);
lean_inc_ref(v_mctx_153_);
lean_dec(v___x_151_);
v_lctx_154_ = lean_ctor_get(v___y_144_, 2);
v_options_155_ = lean_ctor_get(v_toCold_152_, 2);
lean_inc_ref(v_options_155_);
lean_inc_ref(v_lctx_154_);
v___x_156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_156_, 0, v_env_150_);
lean_ctor_set(v___x_156_, 1, v_mctx_153_);
lean_ctor_set(v___x_156_, 2, v_lctx_154_);
lean_ctor_set(v___x_156_, 3, v_options_155_);
v___x_157_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_msgData_143_);
v___x_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3___boxed(lean_object* v_msgData_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3(v_msgData_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(lean_object* v_msg_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_ref_172_; lean_object* v___x_173_; lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_182_; 
v_ref_172_ = lean_ctor_get(v___y_169_, 2);
v___x_173_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2_spec__3(v_msg_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_182_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_182_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
lean_inc(v_ref_172_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v_ref_172_);
lean_ctor_set(v___x_178_, 1, v_a_174_);
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 1);
lean_ctor_set(v___x_176_, 0, v___x_178_);
v___x_180_ = v___x_176_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg___boxed(lean_object* v_msg_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(v_msg_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
lean_object* v_ks_194_; lean_object* v_vs_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_219_; 
v_ks_194_ = lean_ctor_get(v_x_190_, 0);
v_vs_195_ = lean_ctor_get(v_x_190_, 1);
v_isSharedCheck_219_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_219_ == 0)
{
v___x_197_ = v_x_190_;
v_isShared_198_ = v_isSharedCheck_219_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_vs_195_);
lean_inc(v_ks_194_);
lean_dec(v_x_190_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_219_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_array_get_size(v_ks_194_);
v___x_200_ = lean_nat_dec_lt(v_x_191_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
lean_dec(v_x_191_);
v___x_201_ = lean_array_push(v_ks_194_, v_x_192_);
v___x_202_ = lean_array_push(v_vs_195_, v_x_193_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_202_);
lean_ctor_set(v___x_197_, 0, v___x_201_);
v___x_204_ = v___x_197_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_201_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
else
{
lean_object* v_k_x27_206_; uint8_t v___x_207_; 
v_k_x27_206_ = lean_array_fget_borrowed(v_ks_194_, v_x_191_);
v___x_207_ = l_Lean_instBEqMVarId_beq(v_x_192_, v_k_x27_206_);
if (v___x_207_ == 0)
{
lean_object* v___x_209_; 
if (v_isShared_198_ == 0)
{
v___x_209_ = v___x_197_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_ks_194_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v_vs_195_);
v___x_209_ = v_reuseFailAlloc_213_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_add(v_x_191_, v___x_210_);
lean_dec(v_x_191_);
v_x_190_ = v___x_209_;
v_x_191_ = v___x_211_;
goto _start;
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_214_ = lean_array_fset(v_ks_194_, v_x_191_, v_x_192_);
v___x_215_ = lean_array_fset(v_vs_195_, v_x_191_, v_x_193_);
lean_dec(v_x_191_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_215_);
lean_ctor_set(v___x_197_, 0, v___x_214_);
v___x_217_ = v___x_197_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_214_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_n_220_, lean_object* v_k_221_, lean_object* v_v_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_220_, v___x_223_, v_k_221_, v_v_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(lean_object* v_x_226_, size_t v_x_227_, size_t v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_226_) == 0)
{
lean_object* v_es_231_; size_t v___x_232_; size_t v___x_233_; lean_object* v_j_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_es_231_ = lean_ctor_get(v_x_226_, 0);
v___x_232_ = ((size_t)31ULL);
v___x_233_ = lean_usize_land(v_x_227_, v___x_232_);
v_j_234_ = lean_usize_to_nat(v___x_233_);
v___x_235_ = lean_array_get_size(v_es_231_);
v___x_236_ = lean_nat_dec_lt(v_j_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_dec(v_j_234_);
lean_dec(v_x_230_);
lean_dec(v_x_229_);
return v_x_226_;
}
else
{
lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_275_; 
lean_inc_ref(v_es_231_);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v_x_226_, 0);
lean_dec(v_unused_276_);
v___x_238_ = v_x_226_;
v_isShared_239_ = v_isSharedCheck_275_;
goto v_resetjp_237_;
}
else
{
lean_dec(v_x_226_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_275_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_v_240_; lean_object* v___x_241_; lean_object* v_xs_x27_242_; lean_object* v___y_244_; 
v_v_240_ = lean_array_fget(v_es_231_, v_j_234_);
v___x_241_ = lean_box(0);
v_xs_x27_242_ = lean_array_fset(v_es_231_, v_j_234_, v___x_241_);
switch(lean_obj_tag(v_v_240_))
{
case 0:
{
lean_object* v_key_249_; lean_object* v_val_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_260_; 
v_key_249_ = lean_ctor_get(v_v_240_, 0);
v_val_250_ = lean_ctor_get(v_v_240_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_v_240_);
if (v_isSharedCheck_260_ == 0)
{
v___x_252_ = v_v_240_;
v_isShared_253_ = v_isSharedCheck_260_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_val_250_);
lean_inc(v_key_249_);
lean_dec(v_v_240_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_260_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
uint8_t v___x_254_; 
v___x_254_ = l_Lean_instBEqMVarId_beq(v_x_229_, v_key_249_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_256_; 
lean_del_object(v___x_252_);
v___x_255_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_249_, v_val_250_, v_x_229_, v_x_230_);
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
v___y_244_ = v___x_256_;
goto v___jp_243_;
}
else
{
lean_object* v___x_258_; 
lean_dec(v_val_250_);
lean_dec(v_key_249_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_x_230_);
lean_ctor_set(v___x_252_, 0, v_x_229_);
v___x_258_ = v___x_252_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_x_229_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_x_230_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
v___y_244_ = v___x_258_;
goto v___jp_243_;
}
}
}
}
case 1:
{
lean_object* v_node_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_273_; 
v_node_261_ = lean_ctor_get(v_v_240_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_v_240_);
if (v_isSharedCheck_273_ == 0)
{
v___x_263_ = v_v_240_;
v_isShared_264_ = v_isSharedCheck_273_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_node_261_);
lean_dec(v_v_240_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_273_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_265_ = ((size_t)5ULL);
v___x_266_ = lean_usize_shift_right(v_x_227_, v___x_265_);
v___x_267_ = ((size_t)1ULL);
v___x_268_ = lean_usize_add(v_x_228_, v___x_267_);
v___x_269_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_node_261_, v___x_266_, v___x_268_, v_x_229_, v_x_230_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_269_);
v___x_271_ = v___x_263_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
v___y_244_ = v___x_271_;
goto v___jp_243_;
}
}
}
default: 
{
lean_object* v___x_274_; 
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v_x_229_);
lean_ctor_set(v___x_274_, 1, v_x_230_);
v___y_244_ = v___x_274_;
goto v___jp_243_;
}
}
v___jp_243_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = lean_array_fset(v_xs_x27_242_, v_j_234_, v___y_244_);
lean_dec(v_j_234_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_245_);
v___x_247_ = v___x_238_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
else
{
lean_object* v_ks_277_; lean_object* v_vs_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_296_; 
v_ks_277_ = lean_ctor_get(v_x_226_, 0);
v_vs_278_ = lean_ctor_get(v_x_226_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_x_226_);
if (v_isSharedCheck_296_ == 0)
{
v___x_280_ = v_x_226_;
v_isShared_281_ = v_isSharedCheck_296_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_vs_278_);
lean_inc(v_ks_277_);
lean_dec(v_x_226_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_296_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_ks_277_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_vs_278_);
v___x_283_ = v_reuseFailAlloc_295_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v_newNode_284_; size_t v___x_285_; uint8_t v___x_286_; 
v_newNode_284_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(v___x_283_, v_x_229_, v_x_230_);
v___x_285_ = ((size_t)7ULL);
v___x_286_ = lean_usize_dec_le(v___x_285_, v_x_228_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_287_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_284_);
v___x_288_ = lean_unsigned_to_nat(4u);
v___x_289_ = lean_nat_dec_lt(v___x_287_, v___x_288_);
lean_dec(v___x_287_);
if (v___x_289_ == 0)
{
lean_object* v_ks_290_; lean_object* v_vs_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_ks_290_ = lean_ctor_get(v_newNode_284_, 0);
lean_inc_ref(v_ks_290_);
v_vs_291_ = lean_ctor_get(v_newNode_284_, 1);
lean_inc_ref(v_vs_291_);
lean_dec_ref(v_newNode_284_);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_294_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_x_228_, v_ks_290_, v_vs_291_, v___x_292_, v___x_293_);
lean_dec_ref(v_vs_291_);
lean_dec_ref(v_ks_290_);
return v___x_294_;
}
else
{
return v_newNode_284_;
}
}
else
{
return v_newNode_284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_297_, lean_object* v_keys_298_, lean_object* v_vals_299_, lean_object* v_i_300_, lean_object* v_entries_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_array_get_size(v_keys_298_);
v___x_303_ = lean_nat_dec_lt(v_i_300_, v___x_302_);
if (v___x_303_ == 0)
{
lean_dec(v_i_300_);
return v_entries_301_;
}
else
{
lean_object* v_k_304_; lean_object* v_v_305_; uint64_t v___x_306_; size_t v_h_307_; size_t v___x_308_; lean_object* v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v_h_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v_k_304_ = lean_array_fget_borrowed(v_keys_298_, v_i_300_);
v_v_305_ = lean_array_fget_borrowed(v_vals_299_, v_i_300_);
v___x_306_ = l_Lean_instHashableMVarId_hash(v_k_304_);
v_h_307_ = lean_uint64_to_usize(v___x_306_);
v___x_308_ = ((size_t)5ULL);
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = ((size_t)1ULL);
v___x_311_ = lean_usize_sub(v_depth_297_, v___x_310_);
v___x_312_ = lean_usize_mul(v___x_308_, v___x_311_);
v_h_313_ = lean_usize_shift_right(v_h_307_, v___x_312_);
v___x_314_ = lean_nat_add(v_i_300_, v___x_309_);
lean_dec(v_i_300_);
lean_inc(v_v_305_);
lean_inc(v_k_304_);
v___x_315_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_entries_301_, v_h_313_, v_depth_297_, v_k_304_, v_v_305_);
v_i_300_ = v___x_314_;
v_entries_301_ = v___x_315_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_317_, lean_object* v_keys_318_, lean_object* v_vals_319_, lean_object* v_i_320_, lean_object* v_entries_321_){
_start:
{
size_t v_depth_boxed_322_; lean_object* v_res_323_; 
v_depth_boxed_322_ = lean_unbox_usize(v_depth_317_);
lean_dec(v_depth_317_);
v_res_323_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_322_, v_keys_318_, v_vals_319_, v_i_320_, v_entries_321_);
lean_dec_ref(v_vals_319_);
lean_dec_ref(v_keys_318_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_324_, lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
size_t v_x_5730__boxed_329_; size_t v_x_5731__boxed_330_; lean_object* v_res_331_; 
v_x_5730__boxed_329_ = lean_unbox_usize(v_x_325_);
lean_dec(v_x_325_);
v_x_5731__boxed_330_ = lean_unbox_usize(v_x_326_);
lean_dec(v_x_326_);
v_res_331_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_324_, v_x_5730__boxed_329_, v_x_5731__boxed_330_, v_x_327_, v_x_328_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(lean_object* v_x_332_, lean_object* v_x_333_, lean_object* v_x_334_){
_start:
{
uint64_t v___x_335_; size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_335_ = l_Lean_instHashableMVarId_hash(v_x_333_);
v___x_336_ = lean_uint64_to_usize(v___x_335_);
v___x_337_ = ((size_t)1ULL);
v___x_338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_332_, v___x_336_, v___x_337_, v_x_333_, v_x_334_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(lean_object* v_mvarId_339_, lean_object* v_val_340_, lean_object* v___y_341_){
_start:
{
lean_object* v___x_343_; lean_object* v_mctx_344_; lean_object* v_cache_345_; lean_object* v_zetaDeltaFVarIds_346_; lean_object* v_postponed_347_; lean_object* v_diag_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_377_; 
v___x_343_ = lean_st_ref_take(v___y_341_);
v_mctx_344_ = lean_ctor_get(v___x_343_, 0);
v_cache_345_ = lean_ctor_get(v___x_343_, 1);
v_zetaDeltaFVarIds_346_ = lean_ctor_get(v___x_343_, 2);
v_postponed_347_ = lean_ctor_get(v___x_343_, 3);
v_diag_348_ = lean_ctor_get(v___x_343_, 4);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_377_ == 0)
{
v___x_350_ = v___x_343_;
v_isShared_351_ = v_isSharedCheck_377_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_diag_348_);
lean_inc(v_postponed_347_);
lean_inc(v_zetaDeltaFVarIds_346_);
lean_inc(v_cache_345_);
lean_inc(v_mctx_344_);
lean_dec(v___x_343_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_377_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v_depth_352_; lean_object* v_levelAssignDepth_353_; lean_object* v_lmvarCounter_354_; lean_object* v_mvarCounter_355_; lean_object* v_lDecls_356_; lean_object* v_decls_357_; lean_object* v_userNames_358_; lean_object* v_lAssignment_359_; lean_object* v_eAssignment_360_; lean_object* v_dAssignment_361_; lean_object* v_instanceTypedMVars_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_376_; 
v_depth_352_ = lean_ctor_get(v_mctx_344_, 0);
v_levelAssignDepth_353_ = lean_ctor_get(v_mctx_344_, 1);
v_lmvarCounter_354_ = lean_ctor_get(v_mctx_344_, 2);
v_mvarCounter_355_ = lean_ctor_get(v_mctx_344_, 3);
v_lDecls_356_ = lean_ctor_get(v_mctx_344_, 4);
v_decls_357_ = lean_ctor_get(v_mctx_344_, 5);
v_userNames_358_ = lean_ctor_get(v_mctx_344_, 6);
v_lAssignment_359_ = lean_ctor_get(v_mctx_344_, 7);
v_eAssignment_360_ = lean_ctor_get(v_mctx_344_, 8);
v_dAssignment_361_ = lean_ctor_get(v_mctx_344_, 9);
v_instanceTypedMVars_362_ = lean_ctor_get(v_mctx_344_, 10);
v_isSharedCheck_376_ = !lean_is_exclusive(v_mctx_344_);
if (v_isSharedCheck_376_ == 0)
{
v___x_364_ = v_mctx_344_;
v_isShared_365_ = v_isSharedCheck_376_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_instanceTypedMVars_362_);
lean_inc(v_dAssignment_361_);
lean_inc(v_eAssignment_360_);
lean_inc(v_lAssignment_359_);
lean_inc(v_userNames_358_);
lean_inc(v_decls_357_);
lean_inc(v_lDecls_356_);
lean_inc(v_mvarCounter_355_);
lean_inc(v_lmvarCounter_354_);
lean_inc(v_levelAssignDepth_353_);
lean_inc(v_depth_352_);
lean_dec(v_mctx_344_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_376_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(v_eAssignment_360_, v_mvarId_339_, v_val_340_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 8, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_depth_352_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_levelAssignDepth_353_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_lmvarCounter_354_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_mvarCounter_355_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_lDecls_356_);
lean_ctor_set(v_reuseFailAlloc_375_, 5, v_decls_357_);
lean_ctor_set(v_reuseFailAlloc_375_, 6, v_userNames_358_);
lean_ctor_set(v_reuseFailAlloc_375_, 7, v_lAssignment_359_);
lean_ctor_set(v_reuseFailAlloc_375_, 8, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_375_, 9, v_dAssignment_361_);
lean_ctor_set(v_reuseFailAlloc_375_, 10, v_instanceTypedMVars_362_);
v___x_368_ = v_reuseFailAlloc_375_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_368_);
v___x_370_ = v___x_350_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_cache_345_);
lean_ctor_set(v_reuseFailAlloc_374_, 2, v_zetaDeltaFVarIds_346_);
lean_ctor_set(v_reuseFailAlloc_374_, 3, v_postponed_347_);
lean_ctor_set(v_reuseFailAlloc_374_, 4, v_diag_348_);
v___x_370_ = v_reuseFailAlloc_374_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = lean_st_ref_put(v___y_341_, v___x_370_);
v___x_372_ = lean_box(0);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg___boxed(lean_object* v_mvarId_378_, lean_object* v_val_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(v_mvarId_378_, v_val_379_, v___y_380_);
lean_dec(v___y_380_);
return v_res_382_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__5));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0(lean_object* v_a_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; 
lean_inc(v_a_395_);
v___x_405_ = l_Lean_MVarId_getType(v_a_395_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_407_; lean_object* v_a_408_; lean_object* v___x_409_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_405_, 1);
v___x_407_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg(v_a_406_, v___y_401_);
v_a_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_a_408_);
lean_dec_ref(v___x_407_);
v___x_409_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_408_);
lean_dec(v_a_408_);
if (lean_obj_tag(v___x_409_) == 1)
{
lean_object* v_val_410_; lean_object* v_u_411_; lean_object* v_00_u03c3s_412_; lean_object* v_hyps_413_; lean_object* v_target_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_443_; 
v_val_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_val_410_);
lean_dec_ref_known(v___x_409_, 1);
v_u_411_ = lean_ctor_get(v_val_410_, 0);
v_00_u03c3s_412_ = lean_ctor_get(v_val_410_, 1);
v_hyps_413_ = lean_ctor_get(v_val_410_, 2);
v_target_414_ = lean_ctor_get(v_val_410_, 3);
v_isSharedCheck_443_ = !lean_is_exclusive(v_val_410_);
if (v_isSharedCheck_443_ == 0)
{
v___x_416_ = v_val_410_;
v_isShared_417_ = v_isSharedCheck_443_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_target_414_);
lean_inc(v_hyps_413_);
lean_inc(v_00_u03c3s_412_);
lean_inc(v_u_411_);
lean_dec(v_val_410_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_443_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_420_; 
lean_inc_ref_n(v_00_u03c3s_412_, 2);
lean_inc_n(v_u_411_, 2);
v___x_418_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp(v_u_411_, v_00_u03c3s_412_);
lean_inc_ref(v_hyps_413_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 3, v___x_418_);
v___x_420_ = v___x_416_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_u_411_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_00_u03c3s_412_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_hyps_413_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v___x_418_);
v___x_420_ = v_reuseFailAlloc_442_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_420_);
v___x_422_ = lean_box(0);
v___x_423_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_421_, v___x_422_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc_n(v_a_424_, 2);
lean_dec_ref_known(v___x_423_, 1);
v___x_425_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4));
v___x_426_ = lean_box(0);
v___x_427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_427_, 0, v_u_411_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_mkConst(v___x_425_, v___x_427_);
v___x_429_ = l_Lean_mkApp4(v___x_428_, v_00_u03c3s_412_, v_hyps_413_, v_target_414_, v_a_424_);
v___x_430_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(v_a_395_, v___x_429_, v___y_401_);
lean_dec_ref(v___x_430_);
v___x_431_ = l_Lean_Expr_mvarId_x21(v_a_424_);
lean_dec(v_a_424_);
v___x_432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_426_);
v___x_433_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_432_, v___y_397_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
return v___x_433_;
}
else
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_target_414_);
lean_dec_ref(v_hyps_413_);
lean_dec_ref(v_00_u03c3s_412_);
lean_dec(v_u_411_);
lean_dec(v_a_395_);
v_a_434_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_423_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_423_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec(v___x_409_);
lean_dec(v_a_395_);
v___x_444_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6);
v___x_445_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(v___x_444_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
return v___x_445_;
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec(v_a_395_);
v_a_446_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_405_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_405_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___boxed(lean_object* v_a_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0(v_a_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_466_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___f_476_; lean_object* v___x_477_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc_n(v_a_475_, 2);
lean_dec_ref_known(v___x_474_, 1);
v___f_476_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_476_, 0, v_a_475_);
v___x_477_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg(v_a_475_, v___f_476_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
return v___x_477_;
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v_a_478_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_474_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_474_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___boxed(lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec_ref(v_a_490_);
lean_dec(v_a_489_);
lean_dec_ref(v_a_488_);
lean_dec(v_a_487_);
lean_dec_ref(v_a_486_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso(lean_object* v_x_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(v_a_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___boxed(lean_object* v_x_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso(v_x_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_x_507_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1(lean_object* v_mvarId_518_, lean_object* v_val_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(v_mvarId_518_, v_val_519_, v___y_525_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___boxed(lean_object* v_mvarId_530_, lean_object* v_val_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1(v_mvarId_530_, v_val_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec(v___y_535_);
lean_dec_ref(v___y_534_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2(lean_object* v_00_u03b1_542_, lean_object* v_msg_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(v_msg_543_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___boxed(lean_object* v_00_u03b1_554_, lean_object* v_msg_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2(v_00_u03b1_554_, v_msg_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1(lean_object* v_00_u03b2_566_, lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(v_x_567_, v_x_568_, v_x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_571_, lean_object* v_x_572_, size_t v_x_573_, size_t v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_572_, v_x_573_, v_x_574_, v_x_575_, v_x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_578_, lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
size_t v_x_6200__boxed_584_; size_t v_x_6201__boxed_585_; lean_object* v_res_586_; 
v_x_6200__boxed_584_ = lean_unbox_usize(v_x_580_);
lean_dec(v_x_580_);
v_x_6201__boxed_585_ = lean_unbox_usize(v_x_581_);
lean_dec(v_x_581_);
v_res_586_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3(v_00_u03b2_578_, v_x_579_, v_x_6200__boxed_584_, v_x_6201__boxed_585_, v_x_582_, v_x_583_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_587_, lean_object* v_n_588_, lean_object* v_k_589_, lean_object* v_v_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(v_n_588_, v_k_589_, v_v_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_592_, size_t v_depth_593_, lean_object* v_keys_594_, lean_object* v_vals_595_, lean_object* v_heq_596_, lean_object* v_i_597_, lean_object* v_entries_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_593_, v_keys_594_, v_vals_595_, v_i_597_, v_entries_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_600_, lean_object* v_depth_601_, lean_object* v_keys_602_, lean_object* v_vals_603_, lean_object* v_heq_604_, lean_object* v_i_605_, lean_object* v_entries_606_){
_start:
{
size_t v_depth_boxed_607_; lean_object* v_res_608_; 
v_depth_boxed_607_ = lean_unbox_usize(v_depth_601_);
lean_dec(v_depth_601_);
v_res_608_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_600_, v_depth_boxed_607_, v_keys_602_, v_vals_603_, v_heq_604_, v_i_605_, v_entries_606_);
lean_dec_ref(v_vals_603_);
lean_dec_ref(v_keys_602_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_610_, v_x_611_, v_x_612_, v_x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1(){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_635_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_636_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4));
v___x_637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8));
v___x_638_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___boxed), 10, 0);
v___x_639_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_635_, v___x_636_, v___x_637_, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___boxed(lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1();
return v_res_641_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Exfalso(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1();
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
