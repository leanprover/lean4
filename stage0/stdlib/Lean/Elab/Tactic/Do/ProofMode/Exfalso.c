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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(lean_object* v_x_225_, size_t v_x_226_, size_t v_x_227_, lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_225_) == 0)
{
lean_object* v_es_230_; size_t v___x_231_; size_t v___x_232_; lean_object* v_j_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_es_230_ = lean_ctor_get(v_x_225_, 0);
v___x_231_ = ((size_t)31ULL);
v___x_232_ = lean_usize_land(v_x_226_, v___x_231_);
v_j_233_ = lean_usize_to_nat(v___x_232_);
v___x_234_ = lean_array_get_size(v_es_230_);
v___x_235_ = lean_nat_dec_lt(v_j_233_, v___x_234_);
if (v___x_235_ == 0)
{
lean_dec(v_j_233_);
lean_dec(v_x_229_);
lean_dec(v_x_228_);
return v_x_225_;
}
else
{
lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_274_; 
lean_inc_ref(v_es_230_);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v_x_225_, 0);
lean_dec(v_unused_275_);
v___x_237_ = v_x_225_;
v_isShared_238_ = v_isSharedCheck_274_;
goto v_resetjp_236_;
}
else
{
lean_dec(v_x_225_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_274_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_v_239_; lean_object* v___x_240_; lean_object* v_xs_x27_241_; lean_object* v___y_243_; 
v_v_239_ = lean_array_fget(v_es_230_, v_j_233_);
v___x_240_ = lean_box(0);
v_xs_x27_241_ = lean_array_fset(v_es_230_, v_j_233_, v___x_240_);
switch(lean_obj_tag(v_v_239_))
{
case 0:
{
lean_object* v_key_248_; lean_object* v_val_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_259_; 
v_key_248_ = lean_ctor_get(v_v_239_, 0);
v_val_249_ = lean_ctor_get(v_v_239_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_v_239_);
if (v_isSharedCheck_259_ == 0)
{
v___x_251_ = v_v_239_;
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_val_249_);
lean_inc(v_key_248_);
lean_dec(v_v_239_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
uint8_t v___x_253_; 
v___x_253_ = l_Lean_instBEqMVarId_beq(v_x_228_, v_key_248_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_del_object(v___x_251_);
v___x_254_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_248_, v_val_249_, v_x_228_, v_x_229_);
v___x_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
v___y_243_ = v___x_255_;
goto v___jp_242_;
}
else
{
lean_object* v___x_257_; 
lean_dec(v_val_249_);
lean_dec(v_key_248_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_x_229_);
lean_ctor_set(v___x_251_, 0, v_x_228_);
v___x_257_ = v___x_251_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_x_228_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_x_229_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
v___y_243_ = v___x_257_;
goto v___jp_242_;
}
}
}
}
case 1:
{
lean_object* v_node_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_272_; 
v_node_260_ = lean_ctor_get(v_v_239_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v_v_239_);
if (v_isSharedCheck_272_ == 0)
{
v___x_262_ = v_v_239_;
v_isShared_263_ = v_isSharedCheck_272_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_node_260_);
lean_dec(v_v_239_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_272_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_264_ = ((size_t)5ULL);
v___x_265_ = lean_usize_shift_right(v_x_226_, v___x_264_);
v___x_266_ = ((size_t)1ULL);
v___x_267_ = lean_usize_add(v_x_227_, v___x_266_);
v___x_268_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_node_260_, v___x_265_, v___x_267_, v_x_228_, v_x_229_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_268_);
v___x_270_ = v___x_262_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
v___y_243_ = v___x_270_;
goto v___jp_242_;
}
}
}
default: 
{
lean_object* v___x_273_; 
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_x_228_);
lean_ctor_set(v___x_273_, 1, v_x_229_);
v___y_243_ = v___x_273_;
goto v___jp_242_;
}
}
v___jp_242_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_array_fset(v_xs_x27_241_, v_j_233_, v___y_243_);
lean_dec(v_j_233_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_244_);
v___x_246_ = v___x_237_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
}
else
{
lean_object* v_ks_276_; lean_object* v_vs_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_297_; 
v_ks_276_ = lean_ctor_get(v_x_225_, 0);
v_vs_277_ = lean_ctor_get(v_x_225_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_297_ == 0)
{
v___x_279_ = v_x_225_;
v_isShared_280_ = v_isSharedCheck_297_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_vs_277_);
lean_inc(v_ks_276_);
lean_dec(v_x_225_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_297_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_ks_276_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_vs_277_);
v___x_282_ = v_reuseFailAlloc_296_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v_newNode_283_; uint8_t v___y_285_; size_t v___x_291_; uint8_t v___x_292_; 
v_newNode_283_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(v___x_282_, v_x_228_, v_x_229_);
v___x_291_ = ((size_t)7ULL);
v___x_292_ = lean_usize_dec_le(v___x_291_, v_x_227_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_293_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_283_);
v___x_294_ = lean_unsigned_to_nat(4u);
v___x_295_ = lean_nat_dec_lt(v___x_293_, v___x_294_);
lean_dec(v___x_293_);
v___y_285_ = v___x_295_;
goto v___jp_284_;
}
else
{
v___y_285_ = v___x_292_;
goto v___jp_284_;
}
v___jp_284_:
{
if (v___y_285_ == 0)
{
lean_object* v_ks_286_; lean_object* v_vs_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_ks_286_ = lean_ctor_get(v_newNode_283_, 0);
lean_inc_ref(v_ks_286_);
v_vs_287_ = lean_ctor_get(v_newNode_283_, 1);
lean_inc_ref(v_vs_287_);
lean_dec_ref(v_newNode_283_);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___closed__0);
v___x_290_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_x_227_, v_ks_286_, v_vs_287_, v___x_288_, v___x_289_);
lean_dec_ref(v_vs_287_);
lean_dec_ref(v_ks_286_);
return v___x_290_;
}
else
{
return v_newNode_283_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(size_t v_depth_298_, lean_object* v_keys_299_, lean_object* v_vals_300_, lean_object* v_i_301_, lean_object* v_entries_302_){
_start:
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_array_get_size(v_keys_299_);
v___x_304_ = lean_nat_dec_lt(v_i_301_, v___x_303_);
if (v___x_304_ == 0)
{
lean_dec(v_i_301_);
return v_entries_302_;
}
else
{
lean_object* v_k_305_; lean_object* v_v_306_; uint64_t v___x_307_; size_t v_h_308_; size_t v___x_309_; lean_object* v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v_h_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_k_305_ = lean_array_fget_borrowed(v_keys_299_, v_i_301_);
v_v_306_ = lean_array_fget_borrowed(v_vals_300_, v_i_301_);
v___x_307_ = l_Lean_instHashableMVarId_hash(v_k_305_);
v_h_308_ = lean_uint64_to_usize(v___x_307_);
v___x_309_ = ((size_t)5ULL);
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_sub(v_depth_298_, v___x_311_);
v___x_313_ = lean_usize_mul(v___x_309_, v___x_312_);
v_h_314_ = lean_usize_shift_right(v_h_308_, v___x_313_);
v___x_315_ = lean_nat_add(v_i_301_, v___x_310_);
lean_dec(v_i_301_);
lean_inc(v_v_306_);
lean_inc(v_k_305_);
v___x_316_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_entries_302_, v_h_314_, v_depth_298_, v_k_305_, v_v_306_);
v_i_301_ = v___x_315_;
v_entries_302_ = v___x_316_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_depth_318_, lean_object* v_keys_319_, lean_object* v_vals_320_, lean_object* v_i_321_, lean_object* v_entries_322_){
_start:
{
size_t v_depth_boxed_323_; lean_object* v_res_324_; 
v_depth_boxed_323_ = lean_unbox_usize(v_depth_318_);
lean_dec(v_depth_318_);
v_res_324_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_323_, v_keys_319_, v_vals_320_, v_i_321_, v_entries_322_);
lean_dec_ref(v_vals_320_);
lean_dec_ref(v_keys_319_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_){
_start:
{
size_t v_x_5671__boxed_330_; size_t v_x_5672__boxed_331_; lean_object* v_res_332_; 
v_x_5671__boxed_330_ = lean_unbox_usize(v_x_326_);
lean_dec(v_x_326_);
v_x_5672__boxed_331_ = lean_unbox_usize(v_x_327_);
lean_dec(v_x_327_);
v_res_332_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_325_, v_x_5671__boxed_330_, v_x_5672__boxed_331_, v_x_328_, v_x_329_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
uint64_t v___x_336_; size_t v___x_337_; size_t v___x_338_; lean_object* v___x_339_; 
v___x_336_ = l_Lean_instHashableMVarId_hash(v_x_334_);
v___x_337_ = lean_uint64_to_usize(v___x_336_);
v___x_338_ = ((size_t)1ULL);
v___x_339_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_333_, v___x_337_, v___x_338_, v_x_334_, v_x_335_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(lean_object* v_mvarId_340_, lean_object* v_val_341_, lean_object* v___y_342_){
_start:
{
lean_object* v___x_344_; lean_object* v_mctx_345_; lean_object* v_cache_346_; lean_object* v_zetaDeltaFVarIds_347_; lean_object* v_postponed_348_; lean_object* v_diag_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_378_; 
v___x_344_ = lean_st_ref_take(v___y_342_);
v_mctx_345_ = lean_ctor_get(v___x_344_, 0);
v_cache_346_ = lean_ctor_get(v___x_344_, 1);
v_zetaDeltaFVarIds_347_ = lean_ctor_get(v___x_344_, 2);
v_postponed_348_ = lean_ctor_get(v___x_344_, 3);
v_diag_349_ = lean_ctor_get(v___x_344_, 4);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_378_ == 0)
{
v___x_351_ = v___x_344_;
v_isShared_352_ = v_isSharedCheck_378_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_diag_349_);
lean_inc(v_postponed_348_);
lean_inc(v_zetaDeltaFVarIds_347_);
lean_inc(v_cache_346_);
lean_inc(v_mctx_345_);
lean_dec(v___x_344_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_378_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_depth_353_; lean_object* v_levelAssignDepth_354_; lean_object* v_lmvarCounter_355_; lean_object* v_mvarCounter_356_; lean_object* v_lDecls_357_; lean_object* v_decls_358_; lean_object* v_userNames_359_; lean_object* v_lAssignment_360_; lean_object* v_eAssignment_361_; lean_object* v_dAssignment_362_; lean_object* v_instanceTypedMVars_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_377_; 
v_depth_353_ = lean_ctor_get(v_mctx_345_, 0);
v_levelAssignDepth_354_ = lean_ctor_get(v_mctx_345_, 1);
v_lmvarCounter_355_ = lean_ctor_get(v_mctx_345_, 2);
v_mvarCounter_356_ = lean_ctor_get(v_mctx_345_, 3);
v_lDecls_357_ = lean_ctor_get(v_mctx_345_, 4);
v_decls_358_ = lean_ctor_get(v_mctx_345_, 5);
v_userNames_359_ = lean_ctor_get(v_mctx_345_, 6);
v_lAssignment_360_ = lean_ctor_get(v_mctx_345_, 7);
v_eAssignment_361_ = lean_ctor_get(v_mctx_345_, 8);
v_dAssignment_362_ = lean_ctor_get(v_mctx_345_, 9);
v_instanceTypedMVars_363_ = lean_ctor_get(v_mctx_345_, 10);
v_isSharedCheck_377_ = !lean_is_exclusive(v_mctx_345_);
if (v_isSharedCheck_377_ == 0)
{
v___x_365_ = v_mctx_345_;
v_isShared_366_ = v_isSharedCheck_377_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_instanceTypedMVars_363_);
lean_inc(v_dAssignment_362_);
lean_inc(v_eAssignment_361_);
lean_inc(v_lAssignment_360_);
lean_inc(v_userNames_359_);
lean_inc(v_decls_358_);
lean_inc(v_lDecls_357_);
lean_inc(v_mvarCounter_356_);
lean_inc(v_lmvarCounter_355_);
lean_inc(v_levelAssignDepth_354_);
lean_inc(v_depth_353_);
lean_dec(v_mctx_345_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_377_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(v_eAssignment_361_, v_mvarId_340_, v_val_341_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 8, v___x_367_);
v___x_369_ = v___x_365_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_depth_353_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_levelAssignDepth_354_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_lmvarCounter_355_);
lean_ctor_set(v_reuseFailAlloc_376_, 3, v_mvarCounter_356_);
lean_ctor_set(v_reuseFailAlloc_376_, 4, v_lDecls_357_);
lean_ctor_set(v_reuseFailAlloc_376_, 5, v_decls_358_);
lean_ctor_set(v_reuseFailAlloc_376_, 6, v_userNames_359_);
lean_ctor_set(v_reuseFailAlloc_376_, 7, v_lAssignment_360_);
lean_ctor_set(v_reuseFailAlloc_376_, 8, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_376_, 9, v_dAssignment_362_);
lean_ctor_set(v_reuseFailAlloc_376_, 10, v_instanceTypedMVars_363_);
v___x_369_ = v_reuseFailAlloc_376_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_371_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_369_);
v___x_371_ = v___x_351_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_369_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_cache_346_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_zetaDeltaFVarIds_347_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_postponed_348_);
lean_ctor_set(v_reuseFailAlloc_375_, 4, v_diag_349_);
v___x_371_ = v_reuseFailAlloc_375_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_372_ = lean_st_ref_put(v___y_342_, v___x_371_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg___boxed(lean_object* v_mvarId_379_, lean_object* v_val_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(v_mvarId_379_, v_val_380_, v___y_381_);
lean_dec(v___y_381_);
return v_res_383_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__5));
v___x_395_ = l_Lean_stringToMessageData(v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0(lean_object* v_a_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; 
lean_inc(v_a_396_);
v___x_406_ = l_Lean_MVarId_getType(v_a_396_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; lean_object* v_a_409_; lean_object* v___x_410_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__0___redArg(v_a_407_, v___y_402_);
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_a_409_);
lean_dec_ref(v___x_408_);
v___x_410_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_409_);
lean_dec(v_a_409_);
if (lean_obj_tag(v___x_410_) == 1)
{
lean_object* v_val_411_; lean_object* v_u_412_; lean_object* v_00_u03c3s_413_; lean_object* v_hyps_414_; lean_object* v_target_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_444_; 
v_val_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_val_411_);
lean_dec_ref_known(v___x_410_, 1);
v_u_412_ = lean_ctor_get(v_val_411_, 0);
v_00_u03c3s_413_ = lean_ctor_get(v_val_411_, 1);
v_hyps_414_ = lean_ctor_get(v_val_411_, 2);
v_target_415_ = lean_ctor_get(v_val_411_, 3);
v_isSharedCheck_444_ = !lean_is_exclusive(v_val_411_);
if (v_isSharedCheck_444_ == 0)
{
v___x_417_ = v_val_411_;
v_isShared_418_ = v_isSharedCheck_444_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_target_415_);
lean_inc(v_hyps_414_);
lean_inc(v_00_u03c3s_413_);
lean_inc(v_u_412_);
lean_dec(v_val_411_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_444_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_421_; 
lean_inc_ref_n(v_00_u03c3s_413_, 2);
lean_inc_n(v_u_412_, 2);
v___x_419_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_falseProp(v_u_412_, v_00_u03c3s_413_);
lean_inc_ref(v_hyps_414_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 3, v___x_419_);
v___x_421_ = v___x_417_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_u_412_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_00_u03c3s_413_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_hyps_414_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v___x_419_);
v___x_421_ = v_reuseFailAlloc_443_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v___x_421_);
v___x_423_ = lean_box(0);
v___x_424_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_422_, v___x_423_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc_n(v_a_425_, 2);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__4));
v___x_427_ = lean_box(0);
v___x_428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_428_, 0, v_u_412_);
lean_ctor_set(v___x_428_, 1, v___x_427_);
v___x_429_ = l_Lean_mkConst(v___x_426_, v___x_428_);
v___x_430_ = l_Lean_mkApp4(v___x_429_, v_00_u03c3s_413_, v_hyps_414_, v_target_415_, v_a_425_);
v___x_431_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(v_a_396_, v___x_430_, v___y_402_);
lean_dec_ref(v___x_431_);
v___x_432_ = l_Lean_Expr_mvarId_x21(v_a_425_);
lean_dec(v_a_425_);
v___x_433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v___x_427_);
v___x_434_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_433_, v___y_398_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
return v___x_434_;
}
else
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
lean_dec_ref(v_target_415_);
lean_dec_ref(v_hyps_414_);
lean_dec_ref(v_00_u03c3s_413_);
lean_dec(v_u_412_);
lean_dec(v_a_396_);
v_a_435_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_424_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_424_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
}
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v___x_410_);
lean_dec(v_a_396_);
v___x_445_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6, &l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___closed__6);
v___x_446_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(v___x_445_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
return v___x_446_;
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v_a_396_);
v_a_447_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_406_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_406_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___boxed(lean_object* v_a_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0(v_a_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v_a_467_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___f_477_; lean_object* v___x_478_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc_n(v_a_476_, 2);
lean_dec_ref_known(v___x_475_, 1);
v___f_477_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_477_, 0, v_a_476_);
v___x_478_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__3___redArg(v_a_476_, v___f_477_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_);
return v___x_478_;
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
v_a_479_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_475_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_475_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg___boxed(lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso(lean_object* v_x_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___redArg(v_a_498_, v_a_499_, v_a_500_, v_a_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___boxed(lean_object* v_x_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso(v_x_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_x_508_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1(lean_object* v_mvarId_519_, lean_object* v_val_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___redArg(v_mvarId_519_, v_val_520_, v___y_526_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1___boxed(lean_object* v_mvarId_531_, lean_object* v_val_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1(v_mvarId_531_, v_val_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2(lean_object* v_00_u03b1_543_, lean_object* v_msg_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___redArg(v_msg_544_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2___boxed(lean_object* v_00_u03b1_555_, lean_object* v_msg_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__2(v_00_u03b1_555_, v_msg_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1(lean_object* v_00_u03b2_567_, lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1___redArg(v_x_568_, v_x_569_, v_x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_572_, lean_object* v_x_573_, size_t v_x_574_, size_t v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___redArg(v_x_573_, v_x_574_, v_x_575_, v_x_576_, v_x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_579_, lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
size_t v_x_6145__boxed_585_; size_t v_x_6146__boxed_586_; lean_object* v_res_587_; 
v_x_6145__boxed_585_ = lean_unbox_usize(v_x_581_);
lean_dec(v_x_581_);
v_x_6146__boxed_586_ = lean_unbox_usize(v_x_582_);
lean_dec(v_x_582_);
v_res_587_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3(v_00_u03b2_579_, v_x_580_, v_x_6145__boxed_585_, v_x_6146__boxed_586_, v_x_583_, v_x_584_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_588_, lean_object* v_n_589_, lean_object* v_k_590_, lean_object* v_v_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6___redArg(v_n_589_, v_k_590_, v_v_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_593_, size_t v_depth_594_, lean_object* v_keys_595_, lean_object* v_vals_596_, lean_object* v_heq_597_, lean_object* v_i_598_, lean_object* v_entries_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_594_, v_keys_595_, v_vals_596_, v_i_598_, v_entries_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_601_, lean_object* v_depth_602_, lean_object* v_keys_603_, lean_object* v_vals_604_, lean_object* v_heq_605_, lean_object* v_i_606_, lean_object* v_entries_607_){
_start:
{
size_t v_depth_boxed_608_; lean_object* v_res_609_; 
v_depth_boxed_608_ = lean_unbox_usize(v_depth_602_);
lean_dec(v_depth_602_);
v_res_609_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_601_, v_depth_boxed_608_, v_keys_603_, v_vals_604_, v_heq_605_, v_i_606_, v_entries_607_);
lean_dec_ref(v_vals_604_);
lean_dec_ref(v_keys_603_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7(lean_object* v_00_u03b2_610_, lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMExfalso_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_611_, v_x_612_, v_x_613_, v_x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1(){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_636_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_637_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__4));
v___x_638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___closed__8));
v___x_639_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___boxed), 10, 0);
v___x_640_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_636_, v___x_637_, v___x_638_, v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1___boxed(lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Exfalso_0__Lean_Elab_Tactic_Do_ProofMode_elabMExfalso___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMExfalso__1();
return v_res_642_;
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
