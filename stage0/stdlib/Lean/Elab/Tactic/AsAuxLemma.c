// Lean compiler output
// Module: Lean.Elab.Tactic.AsAuxLemma
// Imports: public import Lean.Elab.Tactic.Meta
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Tactic_evalTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "Cannot abstract term into auxiliary lemma because there are open goals."};
static const lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_elabAsAuxLemma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_elabAsAuxLemma___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_elabAsAuxLemma___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_elabAsAuxLemma___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "as_aux_lemma"};
static const lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__3_value),LEAN_SCALAR_PTR_LITERAL(248, 107, 244, 71, 211, 100, 179, 147)}};
static const lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_elabAsAuxLemma___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Invalid as_aux_lemma syntax"};
static const lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "elabAsAuxLemma"};
static const lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(18, 164, 209, 194, 176, 214, 145, 116)}};
static const lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___boxed(lean_object*);
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(v_e_31_, v___y_37_);
return v___x_41_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v___y_36_ = stack[5].m_obj;
lean_object* v___y_37_ = stack[6].m_obj;
lean_object* v___y_38_ = stack[7].m_obj;
lean_object* v___y_39_ = stack[8].m_obj;
lean_object* v_res_42_;
v_res_42_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___boxed(lean_object* v_e_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1(v_e_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
lean_object* v_ks_58_; lean_object* v_vs_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_83_; 
v_ks_58_ = lean_ctor_get(v_x_54_, 0);
v_vs_59_ = lean_ctor_get(v_x_54_, 1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_54_);
if (v_isSharedCheck_83_ == 0)
{
v___x_61_ = v_x_54_;
v_isShared_62_ = v_isSharedCheck_83_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_vs_59_);
lean_inc(v_ks_58_);
lean_dec(v_x_54_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_83_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; uint8_t v___x_64_; 
v___x_63_ = lean_array_get_size(v_ks_58_);
v___x_64_ = lean_nat_dec_lt(v_x_55_, v___x_63_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
lean_dec(v_x_55_);
v___x_65_ = lean_array_push(v_ks_58_, v_x_56_);
v___x_66_ = lean_array_push(v_vs_59_, v_x_57_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_66_);
lean_ctor_set(v___x_61_, 0, v___x_65_);
v___x_68_ = v___x_61_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_69_, 1, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
else
{
lean_object* v_k_x27_70_; uint8_t v___x_71_; 
v_k_x27_70_ = lean_array_fget_borrowed(v_ks_58_, v_x_55_);
v___x_71_ = l_Lean_instBEqMVarId_beq(v_x_56_, v_k_x27_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_73_; 
if (v_isShared_62_ == 0)
{
v___x_73_ = v___x_61_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_ks_58_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v_vs_59_);
v___x_73_ = v_reuseFailAlloc_77_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_add(v_x_55_, v___x_74_);
lean_dec(v_x_55_);
v_x_54_ = v___x_73_;
v_x_55_ = v___x_75_;
goto _start;
}
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_78_ = lean_array_fset(v_ks_58_, v_x_55_, v_x_56_);
v___x_79_ = lean_array_fset(v_vs_59_, v_x_55_, v_x_57_);
lean_dec(v_x_55_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_79_);
lean_ctor_set(v___x_61_, 0, v___x_78_);
v___x_81_ = v___x_61_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_n_84_, lean_object* v_k_85_, lean_object* v_v_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_84_, v___x_87_, v_k_85_, v_v_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_89_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(lean_object* v_x_90_, size_t v_x_91_, size_t v_x_92_, lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
lean_object* v_es_95_; size_t v___x_96_; size_t v___x_97_; lean_object* v_j_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_es_95_ = lean_ctor_get(v_x_90_, 0);
v___x_96_ = ((size_t)31ULL);
v___x_97_ = lean_usize_land(v_x_91_, v___x_96_);
v_j_98_ = lean_usize_to_nat(v___x_97_);
v___x_99_ = lean_array_get_size(v_es_95_);
v___x_100_ = lean_nat_dec_lt(v_j_98_, v___x_99_);
if (v___x_100_ == 0)
{
lean_dec(v_j_98_);
lean_dec(v_x_94_);
lean_dec(v_x_93_);
return v_x_90_;
}
else
{
lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_139_; 
lean_inc_ref(v_es_95_);
v_isSharedCheck_139_ = !lean_is_exclusive(v_x_90_);
if (v_isSharedCheck_139_ == 0)
{
lean_object* v_unused_140_; 
v_unused_140_ = lean_ctor_get(v_x_90_, 0);
lean_dec(v_unused_140_);
v___x_102_ = v_x_90_;
v_isShared_103_ = v_isSharedCheck_139_;
goto v_resetjp_101_;
}
else
{
lean_dec(v_x_90_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_139_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_v_104_; lean_object* v___x_105_; lean_object* v_xs_x27_106_; lean_object* v___y_108_; 
v_v_104_ = lean_array_fget(v_es_95_, v_j_98_);
v___x_105_ = lean_box(0);
v_xs_x27_106_ = lean_array_fset(v_es_95_, v_j_98_, v___x_105_);
switch(lean_obj_tag(v_v_104_))
{
case 0:
{
lean_object* v_key_113_; lean_object* v_val_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_124_; 
v_key_113_ = lean_ctor_get(v_v_104_, 0);
v_val_114_ = lean_ctor_get(v_v_104_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v_v_104_);
if (v_isSharedCheck_124_ == 0)
{
v___x_116_ = v_v_104_;
v_isShared_117_ = v_isSharedCheck_124_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_val_114_);
lean_inc(v_key_113_);
lean_dec(v_v_104_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_124_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
uint8_t v___x_118_; 
v___x_118_ = l_Lean_instBEqMVarId_beq(v_x_93_, v_key_113_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_del_object(v___x_116_);
v___x_119_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_113_, v_val_114_, v_x_93_, v_x_94_);
v___x_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
v___y_108_ = v___x_120_;
goto v___jp_107_;
}
else
{
lean_object* v___x_122_; 
lean_dec(v_val_114_);
lean_dec(v_key_113_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v_x_94_);
lean_ctor_set(v___x_116_, 0, v_x_93_);
v___x_122_ = v___x_116_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_x_93_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_x_94_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
v___y_108_ = v___x_122_;
goto v___jp_107_;
}
}
}
}
case 1:
{
lean_object* v_node_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_137_; 
v_node_125_ = lean_ctor_get(v_v_104_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v_v_104_);
if (v_isSharedCheck_137_ == 0)
{
v___x_127_ = v_v_104_;
v_isShared_128_ = v_isSharedCheck_137_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_node_125_);
lean_dec(v_v_104_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_137_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_129_ = ((size_t)5ULL);
v___x_130_ = lean_usize_shift_right(v_x_91_, v___x_129_);
v___x_131_ = ((size_t)1ULL);
v___x_132_ = lean_usize_add(v_x_92_, v___x_131_);
v___x_133_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_node_125_, v___x_130_, v___x_132_, v_x_93_, v_x_94_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_133_);
v___x_135_ = v___x_127_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
v___y_108_ = v___x_135_;
goto v___jp_107_;
}
}
}
default: 
{
lean_object* v___x_138_; 
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v_x_93_);
lean_ctor_set(v___x_138_, 1, v_x_94_);
v___y_108_ = v___x_138_;
goto v___jp_107_;
}
}
v___jp_107_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = lean_array_fset(v_xs_x27_106_, v_j_98_, v___y_108_);
lean_dec(v_j_98_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v___x_109_);
v___x_111_ = v___x_102_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
else
{
lean_object* v_ks_141_; lean_object* v_vs_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_160_; 
v_ks_141_ = lean_ctor_get(v_x_90_, 0);
v_vs_142_ = lean_ctor_get(v_x_90_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_90_);
if (v_isSharedCheck_160_ == 0)
{
v___x_144_ = v_x_90_;
v_isShared_145_ = v_isSharedCheck_160_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_vs_142_);
lean_inc(v_ks_141_);
lean_dec(v_x_90_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_160_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_ks_141_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v_vs_142_);
v___x_147_ = v_reuseFailAlloc_159_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v_newNode_148_; size_t v___x_149_; uint8_t v___x_150_; 
v_newNode_148_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v___x_147_, v_x_93_, v_x_94_);
v___x_149_ = ((size_t)7ULL);
v___x_150_ = lean_usize_dec_le(v___x_149_, v_x_92_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_151_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_148_);
v___x_152_ = lean_unsigned_to_nat(4u);
v___x_153_ = lean_nat_dec_lt(v___x_151_, v___x_152_);
lean_dec(v___x_151_);
if (v___x_153_ == 0)
{
lean_object* v_ks_154_; lean_object* v_vs_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_ks_154_ = lean_ctor_get(v_newNode_148_, 0);
lean_inc_ref(v_ks_154_);
v_vs_155_ = lean_ctor_get(v_newNode_148_, 1);
lean_inc_ref(v_vs_155_);
lean_dec_ref(v_newNode_148_);
v___x_156_ = lean_unsigned_to_nat(0u);
v___x_157_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_x_92_, v_ks_154_, v_vs_155_, v___x_156_, v___x_157_);
lean_dec_ref(v_vs_155_);
lean_dec_ref(v_ks_154_);
return v___x_158_;
}
else
{
return v_newNode_148_;
}
}
else
{
return v_newNode_148_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_90_ = stack[0].m_obj;
size_t v_x_91_ = stack[1].m_num;
size_t v_x_92_ = stack[2].m_num;
lean_object* v_x_93_ = stack[3].m_obj;
lean_object* v_x_94_ = stack[4].m_obj;
lean_object* v_res_161_;
v_res_161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_90_, v_x_91_, v_x_92_, v_x_93_, v_x_94_);
stack->m_obj
 = v_res_161_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(size_t v_depth_162_, lean_object* v_keys_163_, lean_object* v_vals_164_, lean_object* v_i_165_, lean_object* v_entries_166_){
_start:
{
lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_167_ = lean_array_get_size(v_keys_163_);
v___x_168_ = lean_nat_dec_lt(v_i_165_, v___x_167_);
if (v___x_168_ == 0)
{
lean_dec(v_i_165_);
return v_entries_166_;
}
else
{
lean_object* v_k_169_; lean_object* v_v_170_; uint64_t v___x_171_; size_t v_h_172_; size_t v___x_173_; lean_object* v___x_174_; size_t v___x_175_; size_t v___x_176_; size_t v___x_177_; size_t v_h_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_k_169_ = lean_array_fget_borrowed(v_keys_163_, v_i_165_);
v_v_170_ = lean_array_fget_borrowed(v_vals_164_, v_i_165_);
v___x_171_ = l_Lean_instHashableMVarId_hash(v_k_169_);
v_h_172_ = lean_uint64_to_usize(v___x_171_);
v___x_173_ = ((size_t)5ULL);
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = ((size_t)1ULL);
v___x_176_ = lean_usize_sub(v_depth_162_, v___x_175_);
v___x_177_ = lean_usize_mul(v___x_173_, v___x_176_);
v_h_178_ = lean_usize_shift_right(v_h_172_, v___x_177_);
v___x_179_ = lean_nat_add(v_i_165_, v___x_174_);
lean_dec(v_i_165_);
lean_inc(v_v_170_);
lean_inc(v_k_169_);
v___x_180_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_entries_166_, v_h_178_, v_depth_162_, v_k_169_, v_v_170_);
v_i_165_ = v___x_179_;
v_entries_166_ = v___x_180_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_162_ = stack[0].m_num;
lean_object* v_keys_163_ = stack[1].m_obj;
lean_object* v_vals_164_ = stack[2].m_obj;
lean_object* v_i_165_ = stack[3].m_obj;
lean_object* v_entries_166_ = stack[4].m_obj;
lean_object* v_res_182_;
v_res_182_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_162_, v_keys_163_, v_vals_164_, v_i_165_, v_entries_166_);
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_depth_183_, lean_object* v_keys_184_, lean_object* v_vals_185_, lean_object* v_i_186_, lean_object* v_entries_187_){
_start:
{
size_t v_depth_boxed_188_; lean_object* v_res_189_; 
v_depth_boxed_188_ = lean_unbox_usize(v_depth_183_);
lean_dec(v_depth_183_);
v_res_189_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_188_, v_keys_184_, v_vals_185_, v_i_186_, v_entries_187_);
lean_dec_ref(v_vals_185_);
lean_dec_ref(v_keys_184_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
size_t v_x_4234__boxed_195_; size_t v_x_4235__boxed_196_; lean_object* v_res_197_; 
v_x_4234__boxed_195_ = lean_unbox_usize(v_x_191_);
lean_dec(v_x_191_);
v_x_4235__boxed_196_ = lean_unbox_usize(v_x_192_);
lean_dec(v_x_192_);
v_res_197_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_190_, v_x_4234__boxed_195_, v_x_4235__boxed_196_, v_x_193_, v_x_194_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3___redArg(lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
uint64_t v___x_201_; size_t v___x_202_; size_t v___x_203_; lean_object* v___x_204_; 
v___x_201_ = l_Lean_instHashableMVarId_hash(v_x_199_);
v___x_202_ = lean_uint64_to_usize(v___x_201_);
v___x_203_ = ((size_t)1ULL);
v___x_204_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_198_, v___x_202_, v___x_203_, v_x_199_, v_x_200_);
return v___x_204_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(lean_object* v_mvarId_205_, lean_object* v_val_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; lean_object* v_mctx_210_; lean_object* v_cache_211_; lean_object* v_zetaDeltaFVarIds_212_; lean_object* v_postponed_213_; lean_object* v_diag_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_244_; 
v___x_209_ = lean_st_ref_take(v___y_207_);
v_mctx_210_ = lean_ctor_get(v___x_209_, 0);
v_cache_211_ = lean_ctor_get(v___x_209_, 1);
v_zetaDeltaFVarIds_212_ = lean_ctor_get(v___x_209_, 2);
v_postponed_213_ = lean_ctor_get(v___x_209_, 3);
v_diag_214_ = lean_ctor_get(v___x_209_, 4);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_244_ == 0)
{
v___x_216_ = v___x_209_;
v_isShared_217_ = v_isSharedCheck_244_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_diag_214_);
lean_inc(v_postponed_213_);
lean_inc(v_zetaDeltaFVarIds_212_);
lean_inc(v_cache_211_);
lean_inc(v_mctx_210_);
lean_dec(v___x_209_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_244_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v_depth_218_; lean_object* v_levelAssignDepth_219_; lean_object* v_lmvarCounter_220_; lean_object* v_mvarCounter_221_; lean_object* v_lDecls_222_; lean_object* v_decls_223_; lean_object* v_userNames_224_; lean_object* v_lAssignment_225_; lean_object* v_eAssignment_226_; lean_object* v_dAssignment_227_; lean_object* v_instanceTypedMVars_228_; lean_object* v_synthNormMemo_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_243_; 
v_depth_218_ = lean_ctor_get(v_mctx_210_, 0);
v_levelAssignDepth_219_ = lean_ctor_get(v_mctx_210_, 1);
v_lmvarCounter_220_ = lean_ctor_get(v_mctx_210_, 2);
v_mvarCounter_221_ = lean_ctor_get(v_mctx_210_, 3);
v_lDecls_222_ = lean_ctor_get(v_mctx_210_, 4);
v_decls_223_ = lean_ctor_get(v_mctx_210_, 5);
v_userNames_224_ = lean_ctor_get(v_mctx_210_, 6);
v_lAssignment_225_ = lean_ctor_get(v_mctx_210_, 7);
v_eAssignment_226_ = lean_ctor_get(v_mctx_210_, 8);
v_dAssignment_227_ = lean_ctor_get(v_mctx_210_, 9);
v_instanceTypedMVars_228_ = lean_ctor_get(v_mctx_210_, 10);
v_synthNormMemo_229_ = lean_ctor_get(v_mctx_210_, 11);
v_isSharedCheck_243_ = !lean_is_exclusive(v_mctx_210_);
if (v_isSharedCheck_243_ == 0)
{
v___x_231_ = v_mctx_210_;
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_synthNormMemo_229_);
lean_inc(v_instanceTypedMVars_228_);
lean_inc(v_dAssignment_227_);
lean_inc(v_eAssignment_226_);
lean_inc(v_lAssignment_225_);
lean_inc(v_userNames_224_);
lean_inc(v_decls_223_);
lean_inc(v_lDecls_222_);
lean_inc(v_mvarCounter_221_);
lean_inc(v_lmvarCounter_220_);
lean_inc(v_levelAssignDepth_219_);
lean_inc(v_depth_218_);
lean_dec(v_mctx_210_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_243_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_233_ = lean_box(0);
v___x_234_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3___redArg(v_eAssignment_226_, v_mvarId_205_, v_val_206_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 8, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_depth_218_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v_levelAssignDepth_219_);
lean_ctor_set(v_reuseFailAlloc_242_, 2, v_lmvarCounter_220_);
lean_ctor_set(v_reuseFailAlloc_242_, 3, v_mvarCounter_221_);
lean_ctor_set(v_reuseFailAlloc_242_, 4, v_lDecls_222_);
lean_ctor_set(v_reuseFailAlloc_242_, 5, v_decls_223_);
lean_ctor_set(v_reuseFailAlloc_242_, 6, v_userNames_224_);
lean_ctor_set(v_reuseFailAlloc_242_, 7, v_lAssignment_225_);
lean_ctor_set(v_reuseFailAlloc_242_, 8, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_242_, 9, v_dAssignment_227_);
lean_ctor_set(v_reuseFailAlloc_242_, 10, v_instanceTypedMVars_228_);
lean_ctor_set(v_reuseFailAlloc_242_, 11, v_synthNormMemo_229_);
v___x_236_ = v_reuseFailAlloc_242_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v___x_238_; 
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_236_);
v___x_238_ = v___x_216_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_cache_211_);
lean_ctor_set(v_reuseFailAlloc_241_, 2, v_zetaDeltaFVarIds_212_);
lean_ctor_set(v_reuseFailAlloc_241_, 3, v_postponed_213_);
lean_ctor_set(v_reuseFailAlloc_241_, 4, v_diag_214_);
v___x_238_ = v_reuseFailAlloc_241_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_st_ref_put(v___y_207_, v___x_238_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_233_);
return v___x_240_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_205_ = stack[0].m_obj;
lean_object* v_val_206_ = stack[1].m_obj;
lean_object* v___y_207_ = stack[2].m_obj;
lean_object* v_res_245_;
v_res_245_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(v_mvarId_205_, v_val_206_, v___y_207_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg___boxed(lean_object* v_mvarId_246_, lean_object* v_val_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(v_mvarId_246_, v_val_247_, v___y_248_);
lean_dec(v___y_248_);
return v_res_250_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0(lean_object* v_msgData_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; lean_object* v_env_258_; uint8_t v___x_259_; lean_object* v_env_260_; lean_object* v___x_261_; lean_object* v_toCold_262_; lean_object* v_mctx_263_; lean_object* v_lctx_264_; lean_object* v_options_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_257_ = lean_st_ref_get(v___y_255_);
v_env_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc_ref(v_env_258_);
lean_dec(v___x_257_);
v___x_259_ = 0;
v_env_260_ = l_Lean_Environment_setRecordingDeps(v_env_258_, v___x_259_);
v___x_261_ = lean_st_ref_get(v___y_253_);
v_toCold_262_ = lean_ctor_get(v___y_254_, 0);
v_mctx_263_ = lean_ctor_get(v___x_261_, 0);
lean_inc_ref(v_mctx_263_);
lean_dec(v___x_261_);
v_lctx_264_ = lean_ctor_get(v___y_252_, 2);
v_options_265_ = lean_ctor_get(v_toCold_262_, 2);
lean_inc_ref(v_options_265_);
lean_inc_ref(v_lctx_264_);
v___x_266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_266_, 0, v_env_260_);
lean_ctor_set(v___x_266_, 1, v_mctx_263_);
lean_ctor_set(v___x_266_, 2, v_lctx_264_);
lean_ctor_set(v___x_266_, 3, v_options_265_);
v___x_267_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
lean_ctor_set(v___x_267_, 1, v_msgData_251_);
v___x_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_251_ = stack[0].m_obj;
lean_object* v___y_252_ = stack[1].m_obj;
lean_object* v___y_253_ = stack[2].m_obj;
lean_object* v___y_254_ = stack[3].m_obj;
lean_object* v___y_255_ = stack[4].m_obj;
lean_object* v_res_269_;
v_res_269_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0(v_msgData_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0___boxed(lean_object* v_msgData_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0(v_msgData_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_276_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(lean_object* v_msg_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v_ref_283_; lean_object* v___x_284_; lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
v_ref_283_ = lean_ctor_get(v___y_280_, 2);
v___x_284_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0(v_msg_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_293_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
lean_inc(v_ref_283_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_ref_283_);
lean_ctor_set(v___x_289_, 1, v_a_285_);
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 1);
lean_ctor_set(v___x_287_, 0, v___x_289_);
v___x_291_ = v___x_287_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_277_ = stack[0].m_obj;
lean_object* v___y_278_ = stack[1].m_obj;
lean_object* v___y_279_ = stack[2].m_obj;
lean_object* v___y_280_ = stack[3].m_obj;
lean_object* v___y_281_ = stack[4].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v_msg_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg___boxed(lean_object* v_msg_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v_msg_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_301_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__0));
v___x_304_ = l_Lean_stringToMessageData(v___x_303_);
return v___x_304_;
}
}
lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0(uint8_t v___x_305_, lean_object* v___x_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_308_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
if (lean_obj_tag(v___x_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_a_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc_n(v_a_317_, 2);
lean_dec_ref_known(v___x_316_, 1);
v___x_353_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_353_, 0, v___x_306_);
v___x_354_ = l_Lean_Elab_Tactic_run(v_a_317_, v___x_353_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; uint8_t v___x_356_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v___x_356_ = l_List_isEmpty___redArg(v_a_355_);
lean_dec(v_a_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v_a_317_);
v___x_357_ = lean_obj_once(&l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1, &l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1);
v___x_358_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v___x_357_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
return v___x_358_;
}
else
{
v___y_319_ = v___y_307_;
v___y_320_ = v___y_308_;
v___y_321_ = v___y_309_;
v___y_322_ = v___y_310_;
v___y_323_ = v___y_311_;
v___y_324_ = v___y_312_;
v___y_325_ = v___y_313_;
v___y_326_ = v___y_314_;
goto v___jp_318_;
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec(v_a_317_);
v_a_359_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_354_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_354_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
v___jp_318_:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_a_329_; lean_object* v___x_330_; 
lean_inc_n(v_a_317_, 2);
v___x_327_ = l_Lean_mkMVar(v_a_317_);
v___x_328_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(v___x_327_, v___y_324_);
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref(v___x_328_);
v___x_330_ = l_Lean_MVarId_getType(v_a_317_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; uint8_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = 0;
v___x_333_ = lean_box(0);
v___x_334_ = l_Lean_Meta_mkAuxTheorem(v_a_331_, v_a_329_, v___x_332_, v___x_333_, v___x_305_, v___y_323_, v___y_324_, v___y_325_, v___y_326_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_336_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_a_335_);
lean_dec_ref_known(v___x_334_, 1);
v___x_336_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(v_a_317_, v_a_335_, v___y_324_);
return v___x_336_;
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec(v_a_317_);
v_a_337_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_334_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_334_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_a_329_);
lean_dec(v_a_317_);
v_a_345_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_330_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_330_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v___x_306_);
v_a_367_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_316_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_316_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_305_ = stack[0].m_num;
lean_object* v___x_306_ = stack[1].m_obj;
lean_object* v___y_307_ = stack[2].m_obj;
lean_object* v___y_308_ = stack[3].m_obj;
lean_object* v___y_309_ = stack[4].m_obj;
lean_object* v___y_310_ = stack[5].m_obj;
lean_object* v___y_311_ = stack[6].m_obj;
lean_object* v___y_312_ = stack[7].m_obj;
lean_object* v___y_313_ = stack[8].m_obj;
lean_object* v___y_314_ = stack[9].m_obj;
lean_object* v_res_375_;
v_res_375_ = l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0(v___x_305_, v___x_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
stack->m_obj
 = v_res_375_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___boxed(lean_object* v___x_376_, lean_object* v___x_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
uint8_t v___x_4662__boxed_387_; lean_object* v_res_388_; 
v___x_4662__boxed_387_ = lean_unbox(v___x_376_);
v_res_388_ = l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0(v___x_4662__boxed_387_, v___x_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_388_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___closed__5));
v___x_400_ = l_Lean_stringToMessageData(v___x_399_);
return v___x_400_;
}
}
lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma(lean_object* v_x_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4));
lean_inc(v_x_401_);
v___x_412_ = l_Lean_Syntax_isOfKind(v_x_401_, v___x_411_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec(v_x_401_);
v___x_413_ = lean_obj_once(&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6, &l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6_once, _init_l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6);
v___x_414_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v___x_413_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___f_418_; lean_object* v___x_419_; 
v___x_415_ = lean_unsigned_to_nat(2u);
v___x_416_ = l_Lean_Syntax_getArg(v_x_401_, v___x_415_);
lean_dec(v_x_401_);
v___x_417_ = lean_box(v___x_412_);
v___f_418_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___boxed), 11, 2);
lean_closure_set(v___f_418_, 0, v___x_417_);
lean_closure_set(v___f_418_, 1, v___x_416_);
v___x_419_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_418_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_419_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_elabAsAuxLemma_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_401_ = stack[0].m_obj;
lean_object* v_a_402_ = stack[1].m_obj;
lean_object* v_a_403_ = stack[2].m_obj;
lean_object* v_a_404_ = stack[3].m_obj;
lean_object* v_a_405_ = stack[4].m_obj;
lean_object* v_a_406_ = stack[5].m_obj;
lean_object* v_a_407_ = stack[6].m_obj;
lean_object* v_a_408_ = stack[7].m_obj;
lean_object* v_a_409_ = stack[8].m_obj;
lean_object* v_res_420_;
v_res_420_ = l_Lean_Elab_Tactic_elabAsAuxLemma(v_x_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
stack->m_obj
 = v_res_420_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___boxed(lean_object* v_x_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Elab_Tactic_elabAsAuxLemma(v_x_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
return v_res_431_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0(lean_object* v_00_u03b1_432_, lean_object* v_msg_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v_msg_433_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
return v___x_443_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_433_ = stack[1].m_obj;
lean_object* v___y_434_ = stack[2].m_obj;
lean_object* v___y_435_ = stack[3].m_obj;
lean_object* v___y_436_ = stack[4].m_obj;
lean_object* v___y_437_ = stack[5].m_obj;
lean_object* v___y_438_ = stack[6].m_obj;
lean_object* v___y_439_ = stack[7].m_obj;
lean_object* v___y_440_ = stack[8].m_obj;
lean_object* v___y_441_ = stack[9].m_obj;
lean_object* v_res_444_;
v_res_444_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0(lean_box(0), v_msg_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
stack->m_obj
 = v_res_444_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___boxed(lean_object* v_00_u03b1_445_, lean_object* v_msg_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0(v_00_u03b1_445_, v_msg_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
return v_res_456_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2(lean_object* v_mvarId_457_, lean_object* v_val_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(v_mvarId_457_, v_val_458_, v___y_464_);
return v___x_468_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_457_ = stack[0].m_obj;
lean_object* v_val_458_ = stack[1].m_obj;
lean_object* v___y_459_ = stack[2].m_obj;
lean_object* v___y_460_ = stack[3].m_obj;
lean_object* v___y_461_ = stack[4].m_obj;
lean_object* v___y_462_ = stack[5].m_obj;
lean_object* v___y_463_ = stack[6].m_obj;
lean_object* v___y_464_ = stack[7].m_obj;
lean_object* v___y_465_ = stack[8].m_obj;
lean_object* v___y_466_ = stack[9].m_obj;
lean_object* v_res_469_;
v_res_469_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2(v_mvarId_457_, v_val_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
stack->m_obj
 = v_res_469_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___boxed(lean_object* v_mvarId_470_, lean_object* v_val_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2(v_mvarId_470_, v_val_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3(lean_object* v_00_u03b2_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3___redArg(v_x_483_, v_x_484_, v_x_485_);
return v___x_486_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_487_, lean_object* v_x_488_, size_t v_x_489_, size_t v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_488_, v_x_489_, v_x_490_, v_x_491_, v_x_492_);
return v___x_493_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_488_ = stack[1].m_obj;
size_t v_x_489_ = stack[2].m_num;
size_t v_x_490_ = stack[3].m_num;
lean_object* v_x_491_ = stack[4].m_obj;
lean_object* v_x_492_ = stack[5].m_obj;
lean_object* v_res_494_;
v_res_494_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4(lean_box(0), v_x_488_, v_x_489_, v_x_490_, v_x_491_, v_x_492_);
stack->m_obj
 = v_res_494_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_495_, lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_){
_start:
{
size_t v_x_5097__boxed_501_; size_t v_x_5098__boxed_502_; lean_object* v_res_503_; 
v_x_5097__boxed_501_ = lean_unbox_usize(v_x_497_);
lean_dec(v_x_497_);
v_x_5098__boxed_502_ = lean_unbox_usize(v_x_498_);
lean_dec(v_x_498_);
v_res_503_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4(v_00_u03b2_495_, v_x_496_, v_x_5097__boxed_501_, v_x_5098__boxed_502_, v_x_499_, v_x_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_504_, lean_object* v_n_505_, lean_object* v_k_506_, lean_object* v_v_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v_n_505_, v_k_506_, v_v_507_);
return v___x_508_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_509_, size_t v_depth_510_, lean_object* v_keys_511_, lean_object* v_vals_512_, lean_object* v_heq_513_, lean_object* v_i_514_, lean_object* v_entries_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_510_, v_keys_511_, v_vals_512_, v_i_514_, v_entries_515_);
return v___x_516_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_depth_510_ = stack[1].m_num;
lean_object* v_keys_511_ = stack[2].m_obj;
lean_object* v_vals_512_ = stack[3].m_obj;
lean_object* v_i_514_ = stack[5].m_obj;
lean_object* v_entries_515_ = stack[6].m_obj;
lean_object* v_res_517_;
v_res_517_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(lean_box(0), v_depth_510_, v_keys_511_, v_vals_512_, lean_box(0), v_i_514_, v_entries_515_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_518_, lean_object* v_depth_519_, lean_object* v_keys_520_, lean_object* v_vals_521_, lean_object* v_heq_522_, lean_object* v_i_523_, lean_object* v_entries_524_){
_start:
{
size_t v_depth_boxed_525_; lean_object* v_res_526_; 
v_depth_boxed_525_ = lean_unbox_usize(v_depth_519_);
lean_dec(v_depth_519_);
v_res_526_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_518_, v_depth_boxed_525_, v_keys_520_, v_vals_521_, v_heq_522_, v_i_523_, v_entries_524_);
lean_dec_ref(v_vals_521_);
lean_dec_ref(v_keys_520_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_527_, lean_object* v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_, lean_object* v_x_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_528_, v_x_529_, v_x_530_, v_x_531_);
return v___x_532_;
}
}
lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1(){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_541_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_542_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4));
v___x_543_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2));
v___x_544_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsAuxLemma___boxed), 10, 0);
v___x_545_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_541_, v___x_542_, v___x_543_, v___x_544_);
return v___x_545_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_546_;
v_res_546_ = l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1();
stack->m_obj
 = v_res_546_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___boxed(lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1();
return v_res_548_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
}
#ifdef __cplusplus
}
#endif
