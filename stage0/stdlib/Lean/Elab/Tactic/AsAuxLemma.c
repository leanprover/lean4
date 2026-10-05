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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(v_e_30_, v___y_36_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___boxed(lean_object* v_e_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1(v_e_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_x_52_, lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
lean_object* v_ks_56_; lean_object* v_vs_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_81_; 
v_ks_56_ = lean_ctor_get(v_x_52_, 0);
v_vs_57_ = lean_ctor_get(v_x_52_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_81_ == 0)
{
v___x_59_ = v_x_52_;
v_isShared_60_ = v_isSharedCheck_81_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_vs_57_);
lean_inc(v_ks_56_);
lean_dec(v_x_52_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_81_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_61_; uint8_t v___x_62_; 
v___x_61_ = lean_array_get_size(v_ks_56_);
v___x_62_ = lean_nat_dec_lt(v_x_53_, v___x_61_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
lean_dec(v_x_53_);
v___x_63_ = lean_array_push(v_ks_56_, v_x_54_);
v___x_64_ = lean_array_push(v_vs_57_, v_x_55_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___x_64_);
lean_ctor_set(v___x_59_, 0, v___x_63_);
v___x_66_ = v___x_59_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___x_64_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
else
{
lean_object* v_k_x27_68_; uint8_t v___x_69_; 
v_k_x27_68_ = lean_array_fget_borrowed(v_ks_56_, v_x_53_);
v___x_69_ = l_Lean_instBEqMVarId_beq(v_x_54_, v_k_x27_68_);
if (v___x_69_ == 0)
{
lean_object* v___x_71_; 
if (v_isShared_60_ == 0)
{
v___x_71_ = v___x_59_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_ks_56_);
lean_ctor_set(v_reuseFailAlloc_75_, 1, v_vs_57_);
v___x_71_ = v_reuseFailAlloc_75_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_add(v_x_53_, v___x_72_);
lean_dec(v_x_53_);
v_x_52_ = v___x_71_;
v_x_53_ = v___x_73_;
goto _start;
}
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_76_ = lean_array_fset(v_ks_56_, v_x_53_, v_x_54_);
v___x_77_ = lean_array_fset(v_vs_57_, v_x_53_, v_x_55_);
lean_dec(v_x_53_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___x_77_);
lean_ctor_set(v___x_59_, 0, v___x_76_);
v___x_79_ = v___x_59_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_n_82_, lean_object* v_k_83_, lean_object* v_v_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_82_, v___x_85_, v_k_83_, v_v_84_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(lean_object* v_x_88_, size_t v_x_89_, size_t v_x_90_, lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
if (lean_obj_tag(v_x_88_) == 0)
{
lean_object* v_es_93_; size_t v___x_94_; size_t v___x_95_; lean_object* v_j_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_es_93_ = lean_ctor_get(v_x_88_, 0);
v___x_94_ = ((size_t)31ULL);
v___x_95_ = lean_usize_land(v_x_89_, v___x_94_);
v_j_96_ = lean_usize_to_nat(v___x_95_);
v___x_97_ = lean_array_get_size(v_es_93_);
v___x_98_ = lean_nat_dec_lt(v_j_96_, v___x_97_);
if (v___x_98_ == 0)
{
lean_dec(v_j_96_);
lean_dec(v_x_92_);
lean_dec(v_x_91_);
return v_x_88_;
}
else
{
lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_137_; 
lean_inc_ref(v_es_93_);
v_isSharedCheck_137_ = !lean_is_exclusive(v_x_88_);
if (v_isSharedCheck_137_ == 0)
{
lean_object* v_unused_138_; 
v_unused_138_ = lean_ctor_get(v_x_88_, 0);
lean_dec(v_unused_138_);
v___x_100_ = v_x_88_;
v_isShared_101_ = v_isSharedCheck_137_;
goto v_resetjp_99_;
}
else
{
lean_dec(v_x_88_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_137_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v_v_102_; lean_object* v___x_103_; lean_object* v_xs_x27_104_; lean_object* v___y_106_; 
v_v_102_ = lean_array_fget(v_es_93_, v_j_96_);
v___x_103_ = lean_box(0);
v_xs_x27_104_ = lean_array_fset(v_es_93_, v_j_96_, v___x_103_);
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
v___x_116_ = l_Lean_instBEqMVarId_beq(v_x_91_, v_key_111_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_del_object(v___x_114_);
v___x_117_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_111_, v_val_112_, v_x_91_, v_x_92_);
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
lean_ctor_set(v___x_114_, 1, v_x_92_);
lean_ctor_set(v___x_114_, 0, v_x_91_);
v___x_120_ = v___x_114_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_x_91_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_x_92_);
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
lean_object* v_node_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_135_; 
v_node_123_ = lean_ctor_get(v_v_102_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v_v_102_);
if (v_isSharedCheck_135_ == 0)
{
v___x_125_ = v_v_102_;
v_isShared_126_ = v_isSharedCheck_135_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_node_123_);
lean_dec(v_v_102_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_135_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_127_ = ((size_t)5ULL);
v___x_128_ = lean_usize_shift_right(v_x_89_, v___x_127_);
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_add(v_x_90_, v___x_129_);
v___x_131_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_node_123_, v___x_128_, v___x_130_, v_x_91_, v_x_92_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_131_);
v___x_133_ = v___x_125_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
v___y_106_ = v___x_133_;
goto v___jp_105_;
}
}
}
default: 
{
lean_object* v___x_136_; 
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v_x_91_);
lean_ctor_set(v___x_136_, 1, v_x_92_);
v___y_106_ = v___x_136_;
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
lean_object* v_ks_139_; lean_object* v_vs_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_158_; 
v_ks_139_ = lean_ctor_get(v_x_88_, 0);
v_vs_140_ = lean_ctor_get(v_x_88_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_x_88_);
if (v_isSharedCheck_158_ == 0)
{
v___x_142_ = v_x_88_;
v_isShared_143_ = v_isSharedCheck_158_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_vs_140_);
lean_inc(v_ks_139_);
lean_dec(v_x_88_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_158_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_ks_139_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_vs_140_);
v___x_145_ = v_reuseFailAlloc_157_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v_newNode_146_; size_t v___x_147_; uint8_t v___x_148_; 
v_newNode_146_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v___x_145_, v_x_91_, v_x_92_);
v___x_147_ = ((size_t)7ULL);
v___x_148_ = lean_usize_dec_le(v___x_147_, v_x_90_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; 
v___x_149_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_146_);
v___x_150_ = lean_unsigned_to_nat(4u);
v___x_151_ = lean_nat_dec_lt(v___x_149_, v___x_150_);
lean_dec(v___x_149_);
if (v___x_151_ == 0)
{
lean_object* v_ks_152_; lean_object* v_vs_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_ks_152_ = lean_ctor_get(v_newNode_146_, 0);
lean_inc_ref(v_ks_152_);
v_vs_153_ = lean_ctor_get(v_newNode_146_, 1);
lean_inc_ref(v_vs_153_);
lean_dec_ref(v_newNode_146_);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_156_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_x_90_, v_ks_152_, v_vs_153_, v___x_154_, v___x_155_);
lean_dec_ref(v_vs_153_);
lean_dec_ref(v_ks_152_);
return v___x_156_;
}
else
{
return v_newNode_146_;
}
}
else
{
return v_newNode_146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(size_t v_depth_159_, lean_object* v_keys_160_, lean_object* v_vals_161_, lean_object* v_i_162_, lean_object* v_entries_163_){
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
v___x_177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_entries_163_, v_h_175_, v_depth_159_, v_k_166_, v_v_167_);
v_i_162_ = v___x_176_;
v_entries_163_ = v___x_177_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_depth_179_, lean_object* v_keys_180_, lean_object* v_vals_181_, lean_object* v_i_182_, lean_object* v_entries_183_){
_start:
{
size_t v_depth_boxed_184_; lean_object* v_res_185_; 
v_depth_boxed_184_ = lean_unbox_usize(v_depth_179_);
lean_dec(v_depth_179_);
v_res_185_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_184_, v_keys_180_, v_vals_181_, v_i_182_, v_entries_183_);
lean_dec_ref(v_vals_181_);
lean_dec_ref(v_keys_180_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
size_t v_x_4163__boxed_191_; size_t v_x_4164__boxed_192_; lean_object* v_res_193_; 
v_x_4163__boxed_191_ = lean_unbox_usize(v_x_187_);
lean_dec(v_x_187_);
v_x_4164__boxed_192_ = lean_unbox_usize(v_x_188_);
lean_dec(v_x_188_);
v_res_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_186_, v_x_4163__boxed_191_, v_x_4164__boxed_192_, v_x_189_, v_x_190_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3___redArg(lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
uint64_t v___x_197_; size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v___x_197_ = l_Lean_instHashableMVarId_hash(v_x_195_);
v___x_198_ = lean_uint64_to_usize(v___x_197_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_194_, v___x_198_, v___x_199_, v_x_195_, v_x_196_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(lean_object* v_mvarId_201_, lean_object* v_val_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; lean_object* v_mctx_206_; lean_object* v_cache_207_; lean_object* v_zetaDeltaFVarIds_208_; lean_object* v_postponed_209_; lean_object* v_diag_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_240_; 
v___x_205_ = lean_st_ref_take(v___y_203_);
v_mctx_206_ = lean_ctor_get(v___x_205_, 0);
v_cache_207_ = lean_ctor_get(v___x_205_, 1);
v_zetaDeltaFVarIds_208_ = lean_ctor_get(v___x_205_, 2);
v_postponed_209_ = lean_ctor_get(v___x_205_, 3);
v_diag_210_ = lean_ctor_get(v___x_205_, 4);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_240_ == 0)
{
v___x_212_ = v___x_205_;
v_isShared_213_ = v_isSharedCheck_240_;
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
v_isShared_213_ = v_isSharedCheck_240_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_depth_214_; lean_object* v_levelAssignDepth_215_; lean_object* v_lmvarCounter_216_; lean_object* v_mvarCounter_217_; lean_object* v_lDecls_218_; lean_object* v_decls_219_; lean_object* v_userNames_220_; lean_object* v_lAssignment_221_; lean_object* v_eAssignment_222_; lean_object* v_dAssignment_223_; lean_object* v_instanceTypedMVars_224_; lean_object* v_synthNormMemo_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_239_; 
v_depth_214_ = lean_ctor_get(v_mctx_206_, 0);
v_levelAssignDepth_215_ = lean_ctor_get(v_mctx_206_, 1);
v_lmvarCounter_216_ = lean_ctor_get(v_mctx_206_, 2);
v_mvarCounter_217_ = lean_ctor_get(v_mctx_206_, 3);
v_lDecls_218_ = lean_ctor_get(v_mctx_206_, 4);
v_decls_219_ = lean_ctor_get(v_mctx_206_, 5);
v_userNames_220_ = lean_ctor_get(v_mctx_206_, 6);
v_lAssignment_221_ = lean_ctor_get(v_mctx_206_, 7);
v_eAssignment_222_ = lean_ctor_get(v_mctx_206_, 8);
v_dAssignment_223_ = lean_ctor_get(v_mctx_206_, 9);
v_instanceTypedMVars_224_ = lean_ctor_get(v_mctx_206_, 10);
v_synthNormMemo_225_ = lean_ctor_get(v_mctx_206_, 11);
v_isSharedCheck_239_ = !lean_is_exclusive(v_mctx_206_);
if (v_isSharedCheck_239_ == 0)
{
v___x_227_ = v_mctx_206_;
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_synthNormMemo_225_);
lean_inc(v_instanceTypedMVars_224_);
lean_inc(v_dAssignment_223_);
lean_inc(v_eAssignment_222_);
lean_inc(v_lAssignment_221_);
lean_inc(v_userNames_220_);
lean_inc(v_decls_219_);
lean_inc(v_lDecls_218_);
lean_inc(v_mvarCounter_217_);
lean_inc(v_lmvarCounter_216_);
lean_inc(v_levelAssignDepth_215_);
lean_inc(v_depth_214_);
lean_dec(v_mctx_206_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_239_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_229_ = lean_box(0);
v___x_230_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3___redArg(v_eAssignment_222_, v_mvarId_201_, v_val_202_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 8, v___x_230_);
v___x_232_ = v___x_227_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_depth_214_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_levelAssignDepth_215_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_lmvarCounter_216_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_mvarCounter_217_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_lDecls_218_);
lean_ctor_set(v_reuseFailAlloc_238_, 5, v_decls_219_);
lean_ctor_set(v_reuseFailAlloc_238_, 6, v_userNames_220_);
lean_ctor_set(v_reuseFailAlloc_238_, 7, v_lAssignment_221_);
lean_ctor_set(v_reuseFailAlloc_238_, 8, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_238_, 9, v_dAssignment_223_);
lean_ctor_set(v_reuseFailAlloc_238_, 10, v_instanceTypedMVars_224_);
lean_ctor_set(v_reuseFailAlloc_238_, 11, v_synthNormMemo_225_);
v___x_232_ = v_reuseFailAlloc_238_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_234_; 
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v___x_232_);
v___x_234_ = v___x_212_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_237_, 1, v_cache_207_);
lean_ctor_set(v_reuseFailAlloc_237_, 2, v_zetaDeltaFVarIds_208_);
lean_ctor_set(v_reuseFailAlloc_237_, 3, v_postponed_209_);
lean_ctor_set(v_reuseFailAlloc_237_, 4, v_diag_210_);
v___x_234_ = v_reuseFailAlloc_237_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_st_ref_put(v___y_203_, v___x_234_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_229_);
return v___x_236_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg___boxed(lean_object* v_mvarId_241_, lean_object* v_val_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(v_mvarId_241_, v_val_242_, v___y_243_);
lean_dec(v___y_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0(lean_object* v_msgData_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; lean_object* v_env_253_; uint8_t v___x_254_; lean_object* v_env_255_; lean_object* v___x_256_; lean_object* v_toCold_257_; lean_object* v_mctx_258_; lean_object* v_lctx_259_; lean_object* v_options_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_252_ = lean_st_ref_get(v___y_250_);
v_env_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc_ref(v_env_253_);
lean_dec(v___x_252_);
v___x_254_ = 0;
v_env_255_ = l_Lean_Environment_setRecordingDeps(v_env_253_, v___x_254_);
v___x_256_ = lean_st_ref_get(v___y_248_);
v_toCold_257_ = lean_ctor_get(v___y_249_, 0);
v_mctx_258_ = lean_ctor_get(v___x_256_, 0);
lean_inc_ref(v_mctx_258_);
lean_dec(v___x_256_);
v_lctx_259_ = lean_ctor_get(v___y_247_, 2);
v_options_260_ = lean_ctor_get(v_toCold_257_, 2);
lean_inc_ref(v_options_260_);
lean_inc_ref(v_lctx_259_);
v___x_261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_261_, 0, v_env_255_);
lean_ctor_set(v___x_261_, 1, v_mctx_258_);
lean_ctor_set(v___x_261_, 2, v_lctx_259_);
lean_ctor_set(v___x_261_, 3, v_options_260_);
v___x_262_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_261_);
lean_ctor_set(v___x_262_, 1, v_msgData_246_);
v___x_263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0___boxed(lean_object* v_msgData_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0(v_msgData_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(lean_object* v_msg_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_ref_277_; lean_object* v___x_278_; lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_ref_277_ = lean_ctor_get(v___y_274_, 2);
v___x_278_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0(v_msg_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_287_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
lean_inc(v_ref_277_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_ref_277_);
lean_ctor_set(v___x_283_, 1, v_a_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 1);
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg___boxed(lean_object* v_msg_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v_msg_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_294_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_296_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__0));
v___x_297_ = l_Lean_stringToMessageData(v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0(uint8_t v___x_298_, lean_object* v___x_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_301_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
if (lean_obj_tag(v___x_309_) == 0)
{
lean_object* v_a_310_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_a_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc_n(v_a_310_, 2);
lean_dec_ref_known(v___x_309_, 1);
v___x_346_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_346_, 0, v___x_299_);
v___x_347_ = l_Lean_Elab_Tactic_run(v_a_310_, v___x_346_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; uint8_t v___x_349_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_a_348_);
lean_dec_ref_known(v___x_347_, 1);
v___x_349_ = l_List_isEmpty___redArg(v_a_348_);
lean_dec(v_a_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; 
lean_dec(v_a_310_);
v___x_350_ = lean_obj_once(&l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1, &l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1);
v___x_351_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v___x_350_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
return v___x_351_;
}
else
{
v___y_312_ = v___y_300_;
v___y_313_ = v___y_301_;
v___y_314_ = v___y_302_;
v___y_315_ = v___y_303_;
v___y_316_ = v___y_304_;
v___y_317_ = v___y_305_;
v___y_318_ = v___y_306_;
v___y_319_ = v___y_307_;
goto v___jp_311_;
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec(v_a_310_);
v_a_352_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_347_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_347_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
v___jp_311_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v_a_322_; lean_object* v___x_323_; 
lean_inc_n(v_a_310_, 2);
v___x_320_ = l_Lean_mkMVar(v_a_310_);
v___x_321_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(v___x_320_, v___y_317_);
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref(v___x_321_);
v___x_323_ = l_Lean_MVarId_getType(v_a_310_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_323_, 1);
v___x_325_ = 0;
v___x_326_ = lean_box(0);
v___x_327_ = l_Lean_Meta_mkAuxTheorem(v_a_324_, v_a_322_, v___x_325_, v___x_326_, v___x_298_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_329_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_327_, 1);
v___x_329_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(v_a_310_, v_a_328_, v___y_317_);
return v___x_329_;
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
lean_dec(v_a_310_);
v_a_330_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_327_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_327_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_345_; 
lean_dec(v_a_322_);
lean_dec(v_a_310_);
v_a_338_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_345_ == 0)
{
v___x_340_ = v___x_323_;
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_323_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_345_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_343_; 
if (v_isShared_341_ == 0)
{
v___x_343_ = v___x_340_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_a_338_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
lean_dec(v___x_299_);
v_a_360_ = lean_ctor_get(v___x_309_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_309_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_309_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_309_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___boxed(lean_object* v___x_368_, lean_object* v___x_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
uint8_t v___x_4441__boxed_379_; lean_object* v_res_380_; 
v___x_4441__boxed_379_ = lean_unbox(v___x_368_);
v_res_380_ = l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0(v___x_4441__boxed_379_, v___x_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_380_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___closed__5));
v___x_392_ = l_Lean_stringToMessageData(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma(lean_object* v_x_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4));
lean_inc(v_x_393_);
v___x_404_ = l_Lean_Syntax_isOfKind(v_x_393_, v___x_403_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v_x_393_);
v___x_405_ = lean_obj_once(&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6, &l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6_once, _init_l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6);
v___x_406_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v___x_405_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___x_411_; 
v___x_407_ = lean_unsigned_to_nat(2u);
v___x_408_ = l_Lean_Syntax_getArg(v_x_393_, v___x_407_);
lean_dec(v_x_393_);
v___x_409_ = lean_box(v___x_404_);
v___f_410_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___boxed), 11, 2);
lean_closure_set(v___f_410_, 0, v___x_409_);
lean_closure_set(v___f_410_, 1, v___x_408_);
v___x_411_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_410_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___boxed(lean_object* v_x_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Elab_Tactic_elabAsAuxLemma(v_x_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0(lean_object* v_00_u03b1_423_, lean_object* v_msg_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v_msg_424_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___boxed(lean_object* v_00_u03b1_435_, lean_object* v_msg_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0(v_00_u03b1_435_, v_msg_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2(lean_object* v_mvarId_447_, lean_object* v_val_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(v_mvarId_447_, v_val_448_, v___y_454_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___boxed(lean_object* v_mvarId_459_, lean_object* v_val_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2(v_mvarId_459_, v_val_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3(lean_object* v_00_u03b2_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3___redArg(v_x_472_, v_x_473_, v_x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_476_, lean_object* v_x_477_, size_t v_x_478_, size_t v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_477_, v_x_478_, v_x_479_, v_x_480_, v_x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_483_, lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
size_t v_x_4725__boxed_489_; size_t v_x_4726__boxed_490_; lean_object* v_res_491_; 
v_x_4725__boxed_489_ = lean_unbox_usize(v_x_485_);
lean_dec(v_x_485_);
v_x_4726__boxed_490_ = lean_unbox_usize(v_x_486_);
lean_dec(v_x_486_);
v_res_491_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4(v_00_u03b2_483_, v_x_484_, v_x_4725__boxed_489_, v_x_4726__boxed_490_, v_x_487_, v_x_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_492_, lean_object* v_n_493_, lean_object* v_k_494_, lean_object* v_v_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v_n_493_, v_k_494_, v_v_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_497_, size_t v_depth_498_, lean_object* v_keys_499_, lean_object* v_vals_500_, lean_object* v_heq_501_, lean_object* v_i_502_, lean_object* v_entries_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_498_, v_keys_499_, v_vals_500_, v_i_502_, v_entries_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_505_, lean_object* v_depth_506_, lean_object* v_keys_507_, lean_object* v_vals_508_, lean_object* v_heq_509_, lean_object* v_i_510_, lean_object* v_entries_511_){
_start:
{
size_t v_depth_boxed_512_; lean_object* v_res_513_; 
v_depth_boxed_512_ = lean_unbox_usize(v_depth_506_);
lean_dec(v_depth_506_);
v_res_513_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_505_, v_depth_boxed_512_, v_keys_507_, v_vals_508_, v_heq_509_, v_i_510_, v_entries_511_);
lean_dec_ref(v_vals_508_);
lean_dec_ref(v_keys_507_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_514_, lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_515_, v_x_516_, v_x_517_, v_x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1(){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_528_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_529_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4));
v___x_530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2));
v___x_531_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsAuxLemma___boxed), 10, 0);
v___x_532_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_528_, v___x_529_, v___x_530_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___boxed(lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1();
return v_res_534_;
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
