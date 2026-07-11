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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(v_e_31_, v___y_37_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___boxed(lean_object* v_e_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1(v_e_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
lean_dec(v___y_48_);
lean_dec_ref(v___y_47_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_x_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_ks_57_; lean_object* v_vs_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_82_; 
v_ks_57_ = lean_ctor_get(v_x_53_, 0);
v_vs_58_ = lean_ctor_get(v_x_53_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v_x_53_);
if (v_isSharedCheck_82_ == 0)
{
v___x_60_ = v_x_53_;
v_isShared_61_ = v_isSharedCheck_82_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_vs_58_);
lean_inc(v_ks_57_);
lean_dec(v_x_53_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_82_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_array_get_size(v_ks_57_);
v___x_63_ = lean_nat_dec_lt(v_x_54_, v___x_62_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
lean_dec(v_x_54_);
v___x_64_ = lean_array_push(v_ks_57_, v_x_55_);
v___x_65_ = lean_array_push(v_vs_58_, v_x_56_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_65_);
lean_ctor_set(v___x_60_, 0, v___x_64_);
v___x_67_ = v___x_60_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v___x_64_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
else
{
lean_object* v_k_x27_69_; uint8_t v___x_70_; 
v_k_x27_69_ = lean_array_fget_borrowed(v_ks_57_, v_x_54_);
v___x_70_ = l_Lean_instBEqMVarId_beq(v_x_55_, v_k_x27_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_72_; 
if (v_isShared_61_ == 0)
{
v___x_72_ = v___x_60_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v_ks_57_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v_vs_58_);
v___x_72_ = v_reuseFailAlloc_76_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_add(v_x_54_, v___x_73_);
lean_dec(v_x_54_);
v_x_53_ = v___x_72_;
v_x_54_ = v___x_74_;
goto _start;
}
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_77_ = lean_array_fset(v_ks_57_, v_x_54_, v_x_55_);
v___x_78_ = lean_array_fset(v_vs_58_, v_x_54_, v_x_56_);
lean_dec(v_x_54_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 1, v___x_78_);
lean_ctor_set(v___x_60_, 0, v___x_77_);
v___x_80_ = v___x_60_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_78_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_n_83_, lean_object* v_k_84_, lean_object* v_v_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_83_, v___x_86_, v_k_84_, v_v_85_);
return v___x_87_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(lean_object* v_x_89_, size_t v_x_90_, size_t v_x_91_, lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
lean_object* v_es_94_; size_t v___x_95_; size_t v___x_96_; lean_object* v_j_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_es_94_ = lean_ctor_get(v_x_89_, 0);
v___x_95_ = ((size_t)31ULL);
v___x_96_ = lean_usize_land(v_x_90_, v___x_95_);
v_j_97_ = lean_usize_to_nat(v___x_96_);
v___x_98_ = lean_array_get_size(v_es_94_);
v___x_99_ = lean_nat_dec_lt(v_j_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_dec(v_j_97_);
lean_dec(v_x_93_);
lean_dec(v_x_92_);
return v_x_89_;
}
else
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_138_; 
lean_inc_ref(v_es_94_);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_89_);
if (v_isSharedCheck_138_ == 0)
{
lean_object* v_unused_139_; 
v_unused_139_ = lean_ctor_get(v_x_89_, 0);
lean_dec(v_unused_139_);
v___x_101_ = v_x_89_;
v_isShared_102_ = v_isSharedCheck_138_;
goto v_resetjp_100_;
}
else
{
lean_dec(v_x_89_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_138_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_v_103_; lean_object* v___x_104_; lean_object* v_xs_x27_105_; lean_object* v___y_107_; 
v_v_103_ = lean_array_fget(v_es_94_, v_j_97_);
v___x_104_ = lean_box(0);
v_xs_x27_105_ = lean_array_fset(v_es_94_, v_j_97_, v___x_104_);
switch(lean_obj_tag(v_v_103_))
{
case 0:
{
lean_object* v_key_112_; lean_object* v_val_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_123_; 
v_key_112_ = lean_ctor_get(v_v_103_, 0);
v_val_113_ = lean_ctor_get(v_v_103_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_v_103_);
if (v_isSharedCheck_123_ == 0)
{
v___x_115_ = v_v_103_;
v_isShared_116_ = v_isSharedCheck_123_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_val_113_);
lean_inc(v_key_112_);
lean_dec(v_v_103_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_123_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
uint8_t v___x_117_; 
v___x_117_ = l_Lean_instBEqMVarId_beq(v_x_92_, v_key_112_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_del_object(v___x_115_);
v___x_118_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_112_, v_val_113_, v_x_92_, v_x_93_);
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
v___y_107_ = v___x_119_;
goto v___jp_106_;
}
else
{
lean_object* v___x_121_; 
lean_dec(v_val_113_);
lean_dec(v_key_112_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v_x_93_);
lean_ctor_set(v___x_115_, 0, v_x_92_);
v___x_121_ = v___x_115_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_x_92_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_x_93_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
v___y_107_ = v___x_121_;
goto v___jp_106_;
}
}
}
}
case 1:
{
lean_object* v_node_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_136_; 
v_node_124_ = lean_ctor_get(v_v_103_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_v_103_);
if (v_isSharedCheck_136_ == 0)
{
v___x_126_ = v_v_103_;
v_isShared_127_ = v_isSharedCheck_136_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_node_124_);
lean_dec(v_v_103_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_136_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; size_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_128_ = ((size_t)5ULL);
v___x_129_ = lean_usize_shift_right(v_x_90_, v___x_128_);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_add(v_x_91_, v___x_130_);
v___x_132_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_node_124_, v___x_129_, v___x_131_, v_x_92_, v_x_93_);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_132_);
v___x_134_ = v___x_126_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
v___y_107_ = v___x_134_;
goto v___jp_106_;
}
}
}
default: 
{
lean_object* v___x_137_; 
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_x_92_);
lean_ctor_set(v___x_137_, 1, v_x_93_);
v___y_107_ = v___x_137_;
goto v___jp_106_;
}
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_108_ = lean_array_fset(v_xs_x27_105_, v_j_97_, v___y_107_);
lean_dec(v_j_97_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_108_);
v___x_110_ = v___x_101_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
else
{
lean_object* v_ks_140_; lean_object* v_vs_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_161_; 
v_ks_140_ = lean_ctor_get(v_x_89_, 0);
v_vs_141_ = lean_ctor_get(v_x_89_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_x_89_);
if (v_isSharedCheck_161_ == 0)
{
v___x_143_ = v_x_89_;
v_isShared_144_ = v_isSharedCheck_161_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_vs_141_);
lean_inc(v_ks_140_);
lean_dec(v_x_89_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_161_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_ks_140_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_vs_141_);
v___x_146_ = v_reuseFailAlloc_160_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v_newNode_147_; uint8_t v___y_149_; size_t v___x_155_; uint8_t v___x_156_; 
v_newNode_147_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v___x_146_, v_x_92_, v_x_93_);
v___x_155_ = ((size_t)7ULL);
v___x_156_ = lean_usize_dec_le(v___x_155_, v_x_91_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_157_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_147_);
v___x_158_ = lean_unsigned_to_nat(4u);
v___x_159_ = lean_nat_dec_lt(v___x_157_, v___x_158_);
lean_dec(v___x_157_);
v___y_149_ = v___x_159_;
goto v___jp_148_;
}
else
{
v___y_149_ = v___x_156_;
goto v___jp_148_;
}
v___jp_148_:
{
if (v___y_149_ == 0)
{
lean_object* v_ks_150_; lean_object* v_vs_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_ks_150_ = lean_ctor_get(v_newNode_147_, 0);
lean_inc_ref(v_ks_150_);
v_vs_151_ = lean_ctor_get(v_newNode_147_, 1);
lean_inc_ref(v_vs_151_);
lean_dec_ref(v_newNode_147_);
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_154_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_x_91_, v_ks_150_, v_vs_151_, v___x_152_, v___x_153_);
lean_dec_ref(v_vs_151_);
lean_dec_ref(v_ks_150_);
return v___x_154_;
}
else
{
return v_newNode_147_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(size_t v_depth_162_, lean_object* v_keys_163_, lean_object* v_vals_164_, lean_object* v_i_165_, lean_object* v_entries_166_){
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_depth_182_, lean_object* v_keys_183_, lean_object* v_vals_184_, lean_object* v_i_185_, lean_object* v_entries_186_){
_start:
{
size_t v_depth_boxed_187_; lean_object* v_res_188_; 
v_depth_boxed_187_ = lean_unbox_usize(v_depth_182_);
lean_dec(v_depth_182_);
v_res_188_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_187_, v_keys_183_, v_vals_184_, v_i_185_, v_entries_186_);
lean_dec_ref(v_vals_184_);
lean_dec_ref(v_keys_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
size_t v_x_4582__boxed_194_; size_t v_x_4583__boxed_195_; lean_object* v_res_196_; 
v_x_4582__boxed_194_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_x_4583__boxed_195_ = lean_unbox_usize(v_x_191_);
lean_dec(v_x_191_);
v_res_196_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_189_, v_x_4582__boxed_194_, v_x_4583__boxed_195_, v_x_192_, v_x_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3___redArg(lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
uint64_t v___x_200_; size_t v___x_201_; size_t v___x_202_; lean_object* v___x_203_; 
v___x_200_ = l_Lean_instHashableMVarId_hash(v_x_198_);
v___x_201_ = lean_uint64_to_usize(v___x_200_);
v___x_202_ = ((size_t)1ULL);
v___x_203_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_197_, v___x_201_, v___x_202_, v_x_198_, v_x_199_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(lean_object* v_mvarId_204_, lean_object* v_val_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; lean_object* v_mctx_209_; lean_object* v_cache_210_; lean_object* v_zetaDeltaFVarIds_211_; lean_object* v_postponed_212_; lean_object* v_diag_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_241_; 
v___x_208_ = lean_st_ref_take(v___y_206_);
v_mctx_209_ = lean_ctor_get(v___x_208_, 0);
v_cache_210_ = lean_ctor_get(v___x_208_, 1);
v_zetaDeltaFVarIds_211_ = lean_ctor_get(v___x_208_, 2);
v_postponed_212_ = lean_ctor_get(v___x_208_, 3);
v_diag_213_ = lean_ctor_get(v___x_208_, 4);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_241_ == 0)
{
v___x_215_ = v___x_208_;
v_isShared_216_ = v_isSharedCheck_241_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_diag_213_);
lean_inc(v_postponed_212_);
lean_inc(v_zetaDeltaFVarIds_211_);
lean_inc(v_cache_210_);
lean_inc(v_mctx_209_);
lean_dec(v___x_208_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_241_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v_depth_217_; lean_object* v_levelAssignDepth_218_; lean_object* v_lmvarCounter_219_; lean_object* v_mvarCounter_220_; lean_object* v_lDecls_221_; lean_object* v_decls_222_; lean_object* v_userNames_223_; lean_object* v_lAssignment_224_; lean_object* v_eAssignment_225_; lean_object* v_dAssignment_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_240_; 
v_depth_217_ = lean_ctor_get(v_mctx_209_, 0);
v_levelAssignDepth_218_ = lean_ctor_get(v_mctx_209_, 1);
v_lmvarCounter_219_ = lean_ctor_get(v_mctx_209_, 2);
v_mvarCounter_220_ = lean_ctor_get(v_mctx_209_, 3);
v_lDecls_221_ = lean_ctor_get(v_mctx_209_, 4);
v_decls_222_ = lean_ctor_get(v_mctx_209_, 5);
v_userNames_223_ = lean_ctor_get(v_mctx_209_, 6);
v_lAssignment_224_ = lean_ctor_get(v_mctx_209_, 7);
v_eAssignment_225_ = lean_ctor_get(v_mctx_209_, 8);
v_dAssignment_226_ = lean_ctor_get(v_mctx_209_, 9);
v_isSharedCheck_240_ = !lean_is_exclusive(v_mctx_209_);
if (v_isSharedCheck_240_ == 0)
{
v___x_228_ = v_mctx_209_;
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_dAssignment_226_);
lean_inc(v_eAssignment_225_);
lean_inc(v_lAssignment_224_);
lean_inc(v_userNames_223_);
lean_inc(v_decls_222_);
lean_inc(v_lDecls_221_);
lean_inc(v_mvarCounter_220_);
lean_inc(v_lmvarCounter_219_);
lean_inc(v_levelAssignDepth_218_);
lean_inc(v_depth_217_);
lean_dec(v_mctx_209_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_240_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3___redArg(v_eAssignment_225_, v_mvarId_204_, v_val_205_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 8, v___x_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_depth_217_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_levelAssignDepth_218_);
lean_ctor_set(v_reuseFailAlloc_239_, 2, v_lmvarCounter_219_);
lean_ctor_set(v_reuseFailAlloc_239_, 3, v_mvarCounter_220_);
lean_ctor_set(v_reuseFailAlloc_239_, 4, v_lDecls_221_);
lean_ctor_set(v_reuseFailAlloc_239_, 5, v_decls_222_);
lean_ctor_set(v_reuseFailAlloc_239_, 6, v_userNames_223_);
lean_ctor_set(v_reuseFailAlloc_239_, 7, v_lAssignment_224_);
lean_ctor_set(v_reuseFailAlloc_239_, 8, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_239_, 9, v_dAssignment_226_);
v___x_232_ = v_reuseFailAlloc_239_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_234_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 0, v___x_232_);
v___x_234_ = v___x_215_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_cache_210_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_zetaDeltaFVarIds_211_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_postponed_212_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_diag_213_);
v___x_234_ = v_reuseFailAlloc_238_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_st_ref_set(v___y_206_, v___x_234_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg___boxed(lean_object* v_mvarId_242_, lean_object* v_val_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(v_mvarId_242_, v_val_243_, v___y_244_);
lean_dec(v___y_244_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0(lean_object* v_msgData_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; lean_object* v_env_254_; lean_object* v___x_255_; lean_object* v_mctx_256_; lean_object* v_lctx_257_; lean_object* v_options_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_253_ = lean_st_ref_get(v___y_251_);
v_env_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc_ref(v_env_254_);
lean_dec(v___x_253_);
v___x_255_ = lean_st_ref_get(v___y_249_);
v_mctx_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc_ref(v_mctx_256_);
lean_dec(v___x_255_);
v_lctx_257_ = lean_ctor_get(v___y_248_, 2);
v_options_258_ = lean_ctor_get(v___y_250_, 2);
lean_inc_ref(v_options_258_);
lean_inc_ref(v_lctx_257_);
v___x_259_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_259_, 0, v_env_254_);
lean_ctor_set(v___x_259_, 1, v_mctx_256_);
lean_ctor_set(v___x_259_, 2, v_lctx_257_);
lean_ctor_set(v___x_259_, 3, v_options_258_);
v___x_260_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v_msgData_247_);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0___boxed(lean_object* v_msgData_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0(v_msgData_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(lean_object* v_msg_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_ref_275_; lean_object* v___x_276_; lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_285_; 
v_ref_275_ = lean_ctor_get(v___y_272_, 5);
v___x_276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0_spec__0(v_msg_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg___boxed(lean_object* v_msg_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v_msg_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__0));
v___x_295_ = l_Lean_stringToMessageData(v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0(lean_object* v___x_296_, uint8_t v___x_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_299_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v_a_308_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_317_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_a_308_ = lean_ctor_get(v___x_307_, 0);
lean_inc_n(v_a_308_, 2);
lean_dec_ref_known(v___x_307_, 1);
v___x_344_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalTactic___boxed), 10, 1);
lean_closure_set(v___x_344_, 0, v___x_296_);
v___x_345_ = l_Lean_Elab_Tactic_run(v_a_308_, v___x_344_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; uint8_t v___x_347_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v___x_347_ = l_List_isEmpty___redArg(v_a_346_);
lean_dec(v_a_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_a_308_);
v___x_348_ = lean_obj_once(&l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1, &l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___closed__1);
v___x_349_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v___x_348_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
return v___x_349_;
}
else
{
v___y_310_ = v___y_298_;
v___y_311_ = v___y_299_;
v___y_312_ = v___y_300_;
v___y_313_ = v___y_301_;
v___y_314_ = v___y_302_;
v___y_315_ = v___y_303_;
v___y_316_ = v___y_304_;
v___y_317_ = v___y_305_;
goto v___jp_309_;
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_a_308_);
v_a_350_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_345_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_345_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
v___jp_309_:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v_a_320_; lean_object* v___x_321_; 
lean_inc_n(v_a_308_, 2);
v___x_318_ = l_Lean_mkMVar(v_a_308_);
v___x_319_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__1___redArg(v___x_318_, v___y_315_);
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref(v___x_319_);
v___x_321_ = l_Lean_MVarId_getType(v_a_308_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
v___x_323_ = 0;
v___x_324_ = lean_box(0);
v___x_325_ = l_Lean_Meta_mkAuxTheorem(v_a_322_, v_a_320_, v___x_323_, v___x_324_, v___x_297_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
v___x_327_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(v_a_308_, v_a_326_, v___y_315_);
return v___x_327_;
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_335_; 
lean_dec(v_a_308_);
v_a_328_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_335_ == 0)
{
v___x_330_ = v___x_325_;
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v___x_325_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_335_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_334_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
return v___x_333_;
}
}
}
}
else
{
lean_object* v_a_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_343_; 
lean_dec(v_a_320_);
lean_dec(v_a_308_);
v_a_336_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_343_ == 0)
{
v___x_338_ = v___x_321_;
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_a_336_);
lean_dec(v___x_321_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_343_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_341_; 
if (v_isShared_339_ == 0)
{
v___x_341_ = v___x_338_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_a_336_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v___x_296_);
v_a_358_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_307_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_307_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___boxed(lean_object* v___x_366_, lean_object* v___x_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
uint8_t v___x_4863__boxed_377_; lean_object* v_res_378_; 
v___x_4863__boxed_377_ = lean_unbox(v___x_367_);
v_res_378_ = l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0(v___x_366_, v___x_4863__boxed_377_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_378_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___closed__5));
v___x_390_ = l_Lean_stringToMessageData(v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma(lean_object* v_x_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4));
lean_inc(v_x_391_);
v___x_402_ = l_Lean_Syntax_isOfKind(v_x_391_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_x_391_);
v___x_403_ = lean_obj_once(&l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6, &l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6_once, _init_l_Lean_Elab_Tactic_elabAsAuxLemma___closed__6);
v___x_404_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v___x_403_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___f_408_; lean_object* v___x_409_; 
v___x_405_ = lean_unsigned_to_nat(2u);
v___x_406_ = l_Lean_Syntax_getArg(v_x_391_, v___x_405_);
lean_dec(v_x_391_);
v___x_407_ = lean_box(v___x_402_);
v___f_408_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsAuxLemma___lam__0___boxed), 11, 2);
lean_closure_set(v___f_408_, 0, v___x_406_);
lean_closure_set(v___f_408_, 1, v___x_407_);
v___x_409_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_408_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_elabAsAuxLemma___boxed(lean_object* v_x_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Elab_Tactic_elabAsAuxLemma(v_x_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0(lean_object* v_00_u03b1_421_, lean_object* v_msg_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___redArg(v_msg_422_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0___boxed(lean_object* v_00_u03b1_433_, lean_object* v_msg_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__0(v_00_u03b1_433_, v_msg_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2(lean_object* v_mvarId_445_, lean_object* v_val_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___redArg(v_mvarId_445_, v_val_446_, v___y_452_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2___boxed(lean_object* v_mvarId_457_, lean_object* v_val_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2(v_mvarId_457_, v_val_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3(lean_object* v_00_u03b2_469_, lean_object* v_x_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3___redArg(v_x_470_, v_x_471_, v_x_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_474_, lean_object* v_x_475_, size_t v_x_476_, size_t v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_475_, v_x_476_, v_x_477_, v_x_478_, v_x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
size_t v_x_5146__boxed_487_; size_t v_x_5147__boxed_488_; lean_object* v_res_489_; 
v_x_5146__boxed_487_ = lean_unbox_usize(v_x_483_);
lean_dec(v_x_483_);
v_x_5147__boxed_488_ = lean_unbox_usize(v_x_484_);
lean_dec(v_x_484_);
v_res_489_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4(v_00_u03b2_481_, v_x_482_, v_x_5146__boxed_487_, v_x_5147__boxed_488_, v_x_485_, v_x_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_490_, lean_object* v_n_491_, lean_object* v_k_492_, lean_object* v_v_493_){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v_n_491_, v_k_492_, v_v_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_495_, size_t v_depth_496_, lean_object* v_keys_497_, lean_object* v_vals_498_, lean_object* v_heq_499_, lean_object* v_i_500_, lean_object* v_entries_501_){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_496_, v_keys_497_, v_vals_498_, v_i_500_, v_entries_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_503_, lean_object* v_depth_504_, lean_object* v_keys_505_, lean_object* v_vals_506_, lean_object* v_heq_507_, lean_object* v_i_508_, lean_object* v_entries_509_){
_start:
{
size_t v_depth_boxed_510_; lean_object* v_res_511_; 
v_depth_boxed_510_ = lean_unbox_usize(v_depth_504_);
lean_dec(v_depth_504_);
v_res_511_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_503_, v_depth_boxed_510_, v_keys_505_, v_vals_506_, v_heq_507_, v_i_508_, v_entries_509_);
lean_dec_ref(v_vals_506_);
lean_dec_ref(v_keys_505_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_512_, lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_513_, v_x_514_, v_x_515_, v_x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1(){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_526_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_527_ = ((lean_object*)(l_Lean_Elab_Tactic_elabAsAuxLemma___closed__4));
v___x_528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___closed__2));
v___x_529_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabAsAuxLemma___boxed), 10, 0);
v___x_530_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_526_, v___x_527_, v___x_528_, v___x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1___boxed(lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l___private_Lean_Elab_Tactic_AsAuxLemma_0__Lean_Elab_Tactic_elabAsAuxLemma___regBuiltin_Lean_Elab_Tactic_elabAsAuxLemma__1();
return v_res_532_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Meta(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
