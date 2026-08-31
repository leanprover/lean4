// Lean compiler output
// Module: Lean.Data.PersistentHashMap
// Imports: public import Init.Data.Array.BasicAux public import Init.Data.UInt.Basic public import Init.Control.Except public import Init.Data.Array.Basic import Init.Data.String.Defs import Init.Data.ToString.Macro import Init.Data.Array.Lemmas
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
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_mapM_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_finIdxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_entry_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_entry_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ref_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ref_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_null_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_null_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_entries_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_entries_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_collision_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_collision_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_Node_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_PersistentHashMap_instInhabitedNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_instInhabitedNode___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_instInhabitedNode___closed__0_value;
static const lean_ctor_object l_Lean_PersistentHashMap_instInhabitedNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PersistentHashMap_instInhabitedNode___closed__0_value)}};
static const lean_object* l_Lean_PersistentHashMap_instInhabitedNode___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_instInhabitedNode___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_PersistentHashMap_shift;
LEAN_EXPORT size_t l_Lean_PersistentHashMap_branching;
LEAN_EXPORT size_t l_Lean_PersistentHashMap_maxDepth;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_maxCollisions;
static lean_once_cell_t l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_PersistentHashMap_mul2Shift(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mul2Shift___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_PersistentHashMap_div2Shift(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_div2Shift___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_PersistentHashMap_mod2Shift(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mod2Shift___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PersistentHashMap_find_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Data.PersistentHashMap"};
static const lean_object* l_Lean_PersistentHashMap_find_x21___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_find_x21___redArg___closed__0_value;
static const lean_string_object l_Lean_PersistentHashMap_find_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.PersistentHashMap.find!"};
static const lean_object* l_Lean_PersistentHashMap_find_x21___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_find_x21___redArg___closed__1_value;
static const lean_string_object l_Lean_PersistentHashMap_find_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "key is not in the map"};
static const lean_object* l_Lean_PersistentHashMap_find_x21___redArg___closed__2 = (const lean_object*)&l_Lean_PersistentHashMap_find_x21___redArg___closed__2_value;
static lean_once_cell_t l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_find_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_foldl___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__0_value;
static const lean_closure_object l_Lean_PersistentHashMap_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_foldl___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__1_value;
static const lean_closure_object l_Lean_PersistentHashMap_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_foldl___redArg___closed__2 = (const lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__2_value;
static const lean_closure_object l_Lean_PersistentHashMap_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_foldl___redArg___closed__3 = (const lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__3_value;
static const lean_closure_object l_Lean_PersistentHashMap_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_foldl___redArg___closed__4 = (const lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__4_value;
static const lean_closure_object l_Lean_PersistentHashMap_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_foldl___redArg___closed__5 = (const lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__5_value;
static const lean_closure_object l_Lean_PersistentHashMap_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_foldl___redArg___closed__6 = (const lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__6_value;
static const lean_ctor_object l_Lean_PersistentHashMap_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__0_value),((lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__1_value)}};
static const lean_object* l_Lean_PersistentHashMap_foldl___redArg___closed__7 = (const lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__7_value;
static const lean_ctor_object l_Lean_PersistentHashMap_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__7_value),((lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__2_value),((lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__3_value),((lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__4_value),((lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__5_value)}};
static const lean_object* l_Lean_PersistentHashMap_foldl___redArg___closed__8 = (const lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__8_value;
static const lean_ctor_object l_Lean_PersistentHashMap_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__8_value),((lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__6_value)}};
static const lean_object* l_Lean_PersistentHashMap_foldl___redArg___closed__9 = (const lean_object*)&l_Lean_PersistentHashMap_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_forIn___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_forIn___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_forIn___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_forIn___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toList___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_PersistentHashMap_stats___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PersistentHashMap_stats___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_stats___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PersistentHashMap_Stats_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "{ nodes := "};
static const lean_object* l_Lean_PersistentHashMap_Stats_toString___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_Stats_toString___closed__0_value;
static const lean_string_object l_Lean_PersistentHashMap_Stats_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ", null := "};
static const lean_object* l_Lean_PersistentHashMap_Stats_toString___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_Stats_toString___closed__1_value;
static const lean_string_object l_Lean_PersistentHashMap_Stats_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = ", collisions := "};
static const lean_object* l_Lean_PersistentHashMap_Stats_toString___closed__2 = (const lean_object*)&l_Lean_PersistentHashMap_Stats_toString___closed__2_value;
static const lean_string_object l_Lean_PersistentHashMap_Stats_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ", depth := "};
static const lean_object* l_Lean_PersistentHashMap_Stats_toString___closed__3 = (const lean_object*)&l_Lean_PersistentHashMap_Stats_toString___closed__3_value;
static const lean_string_object l_Lean_PersistentHashMap_Stats_toString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_PersistentHashMap_Stats_toString___closed__4 = (const lean_object*)&l_Lean_PersistentHashMap_Stats_toString___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Stats_toString(lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_instToStringStats___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_Stats_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_instToStringStats___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_instToStringStats___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_PersistentHashMap_instToStringStats = (const lean_object*)&l_Lean_PersistentHashMap_instToStringStats___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___redArg___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_PersistentHashMap_Entry_ctorIdx___redArg(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx(lean_object* v_00_u03b1_7_, lean_object* v_00_u03b2_8_, lean_object* v_00_u03c3_9_, lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lean_PersistentHashMap_Entry_ctorIdx___redArg(v_x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___boxed(lean_object* v_00_u03b1_12_, lean_object* v_00_u03b2_13_, lean_object* v_00_u03c3_14_, lean_object* v_x_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_PersistentHashMap_Entry_ctorIdx(v_00_u03b1_12_, v_00_u03b2_13_, v_00_u03c3_14_, v_x_15_);
lean_dec(v_x_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorElim___redArg(lean_object* v_t_17_, lean_object* v_k_18_){
_start:
{
switch(lean_obj_tag(v_t_17_))
{
case 0:
{
lean_object* v_key_19_; lean_object* v_val_20_; lean_object* v___x_21_; 
v_key_19_ = lean_ctor_get(v_t_17_, 0);
lean_inc(v_key_19_);
v_val_20_ = lean_ctor_get(v_t_17_, 1);
lean_inc(v_val_20_);
lean_dec_ref_known(v_t_17_, 2);
v___x_21_ = lean_apply_2(v_k_18_, v_key_19_, v_val_20_);
return v___x_21_;
}
case 1:
{
lean_object* v_node_22_; lean_object* v___x_23_; 
v_node_22_ = lean_ctor_get(v_t_17_, 0);
lean_inc(v_node_22_);
lean_dec_ref_known(v_t_17_, 1);
v___x_23_ = lean_apply_1(v_k_18_, v_node_22_);
return v___x_23_;
}
default: 
{
return v_k_18_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorElim(lean_object* v_00_u03b1_24_, lean_object* v_00_u03b2_25_, lean_object* v_00_u03c3_26_, lean_object* v_motive_27_, lean_object* v_ctorIdx_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_k_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_29_, v_k_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorElim___boxed(lean_object* v_00_u03b1_33_, lean_object* v_00_u03b2_34_, lean_object* v_00_u03c3_35_, lean_object* v_motive_36_, lean_object* v_ctorIdx_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_k_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_PersistentHashMap_Entry_ctorElim(v_00_u03b1_33_, v_00_u03b2_34_, v_00_u03c3_35_, v_motive_36_, v_ctorIdx_37_, v_t_38_, v_h_39_, v_k_40_);
lean_dec(v_ctorIdx_37_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_entry_elim___redArg(lean_object* v_t_42_, lean_object* v_entry_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_42_, v_entry_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_entry_elim(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_00_u03c3_47_, lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_entry_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_49_, v_entry_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ref_elim___redArg(lean_object* v_t_53_, lean_object* v_ref_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_53_, v_ref_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ref_elim(lean_object* v_00_u03b1_56_, lean_object* v_00_u03b2_57_, lean_object* v_00_u03c3_58_, lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_ref_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_60_, v_ref_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_null_elim___redArg(lean_object* v_t_64_, lean_object* v_null_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_64_, v_null_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_null_elim(lean_object* v_00_u03b1_67_, lean_object* v_00_u03b2_68_, lean_object* v_00_u03c3_69_, lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_null_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_71_, v_null_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object* v_00_u03b1_75_, lean_object* v_00_u03b2_76_, lean_object* v_00_u03c3_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = lean_box(2);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___redArg(lean_object* v_x_79_){
_start:
{
if (lean_obj_tag(v_x_79_) == 0)
{
lean_object* v___x_80_; 
v___x_80_ = lean_unsigned_to_nat(0u);
return v___x_80_;
}
else
{
lean_object* v___x_81_; 
v___x_81_ = lean_unsigned_to_nat(1u);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___redArg___boxed(lean_object* v_x_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_PersistentHashMap_Node_ctorIdx___redArg(v_x_82_);
lean_dec_ref(v_x_82_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx(lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_x_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_PersistentHashMap_Node_ctorIdx___redArg(v_x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___boxed(lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_x_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_PersistentHashMap_Node_ctorIdx(v_00_u03b1_88_, v_00_u03b2_89_, v_x_90_);
lean_dec_ref(v_x_90_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim___redArg(lean_object* v_t_92_, lean_object* v_k_93_){
_start:
{
if (lean_obj_tag(v_t_92_) == 0)
{
lean_object* v_es_94_; lean_object* v___x_95_; 
v_es_94_ = lean_ctor_get(v_t_92_, 0);
lean_inc_ref(v_es_94_);
lean_dec_ref_known(v_t_92_, 1);
v___x_95_ = lean_apply_1(v_k_93_, v_es_94_);
return v___x_95_;
}
else
{
lean_object* v_ks_96_; lean_object* v_vs_97_; lean_object* v___x_98_; 
v_ks_96_ = lean_ctor_get(v_t_92_, 0);
lean_inc_ref(v_ks_96_);
v_vs_97_ = lean_ctor_get(v_t_92_, 1);
lean_inc_ref(v_vs_97_);
lean_dec_ref_known(v_t_92_, 2);
v___x_98_ = lean_apply_3(v_k_93_, v_ks_96_, v_vs_97_, lean_box(0));
return v___x_98_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_motive__1_101_, lean_object* v_ctorIdx_102_, lean_object* v_t_103_, lean_object* v_h_104_, lean_object* v_k_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_103_, v_k_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim___boxed(lean_object* v_00_u03b1_107_, lean_object* v_00_u03b2_108_, lean_object* v_motive__1_109_, lean_object* v_ctorIdx_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_k_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_PersistentHashMap_Node_ctorElim(v_00_u03b1_107_, v_00_u03b2_108_, v_motive__1_109_, v_ctorIdx_110_, v_t_111_, v_h_112_, v_k_113_);
lean_dec(v_ctorIdx_110_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_entries_elim___redArg(lean_object* v_t_115_, lean_object* v_entries_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_115_, v_entries_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_entries_elim(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_motive__1_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_entries_123_){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_121_, v_entries_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_collision_elim___redArg(lean_object* v_t_125_, lean_object* v_collision_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_125_, v_collision_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_collision_elim(lean_object* v_00_u03b1_128_, lean_object* v_00_u03b2_129_, lean_object* v_motive__1_130_, lean_object* v_t_131_, lean_object* v_h_132_, lean_object* v_collision_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_131_, v_collision_133_);
return v___x_134_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_object* v_es_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_es_136_ = lean_ctor_get(v_x_135_, 0);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_array_get_size(v_es_136_);
v___x_139_ = lean_nat_dec_lt(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
uint8_t v___x_140_; 
v___x_140_ = 1;
return v___x_140_;
}
else
{
if (v___x_139_ == 0)
{
return v___x_139_;
}
else
{
size_t v___x_141_; size_t v___x_142_; uint8_t v___x_143_; 
v___x_141_ = ((size_t)0ULL);
v___x_142_ = lean_usize_of_nat(v___x_138_);
v___x_143_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_es_136_, v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
return v___x_139_;
}
else
{
uint8_t v___x_144_; 
v___x_144_ = 0;
return v___x_144_;
}
}
}
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(lean_object* v_as_146_, size_t v_i_147_, size_t v_stop_148_){
_start:
{
uint8_t v___x_153_; 
v___x_153_ = lean_usize_dec_eq(v_i_147_, v_stop_148_);
if (v___x_153_ == 0)
{
uint8_t v___x_154_; lean_object* v___x_155_; 
v___x_154_ = 1;
v___x_155_ = lean_array_uget_borrowed(v_as_146_, v_i_147_);
switch(lean_obj_tag(v___x_155_))
{
case 0:
{
return v___x_154_;
}
case 1:
{
lean_object* v_node_156_; uint8_t v___x_157_; 
v_node_156_ = lean_ctor_get(v___x_155_, 0);
v___x_157_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_node_156_);
if (v___x_157_ == 0)
{
return v___x_154_;
}
else
{
goto v___jp_149_;
}
}
default: 
{
goto v___jp_149_;
}
}
}
else
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
v___jp_149_:
{
size_t v___x_150_; size_t v___x_151_; 
v___x_150_ = ((size_t)1ULL);
v___x_151_ = lean_usize_add(v_i_147_, v___x_150_);
v_i_147_ = v___x_151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg___boxed(lean_object* v_as_159_, lean_object* v_i_160_, lean_object* v_stop_161_){
_start:
{
size_t v_i_boxed_162_; size_t v_stop_boxed_163_; uint8_t v_res_164_; lean_object* v_r_165_; 
v_i_boxed_162_ = lean_unbox_usize(v_i_160_);
lean_dec(v_i_160_);
v_stop_boxed_163_ = lean_unbox_usize(v_stop_161_);
lean_dec(v_stop_161_);
v_res_164_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_as_159_, v_i_boxed_162_, v_stop_boxed_163_);
lean_dec_ref(v_as_159_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_isEmpty___redArg___boxed(lean_object* v_x_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_166_);
lean_dec_ref(v_x_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_Node_isEmpty(lean_object* v_00_u03b1_169_, lean_object* v_00_u03b2_170_, lean_object* v_x_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_isEmpty___boxed(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_x_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_Lean_PersistentHashMap_Node_isEmpty(v_00_u03b1_173_, v_00_u03b2_174_, v_x_175_);
lean_dec_ref(v_x_175_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(lean_object* v_00_u03b1_178_, lean_object* v_00_u03b2_179_, lean_object* v_as_180_, size_t v_i_181_, size_t v_stop_182_){
_start:
{
uint8_t v___x_183_; 
v___x_183_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_as_180_, v_i_181_, v_stop_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___boxed(lean_object* v_00_u03b1_184_, lean_object* v_00_u03b2_185_, lean_object* v_as_186_, lean_object* v_i_187_, lean_object* v_stop_188_){
_start:
{
size_t v_i_boxed_189_; size_t v_stop_boxed_190_; uint8_t v_res_191_; lean_object* v_r_192_; 
v_i_boxed_189_ = lean_unbox_usize(v_i_187_);
lean_dec(v_i_187_);
v_stop_boxed_190_ = lean_unbox_usize(v_stop_188_);
lean_dec(v_stop_188_);
v_res_191_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(v_00_u03b1_184_, v_00_u03b2_185_, v_as_186_, v_i_boxed_189_, v_stop_boxed_190_);
lean_dec_ref(v_as_186_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode(lean_object* v_00_u03b1_197_, lean_object* v_00_u03b2_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = ((lean_object*)(l_Lean_PersistentHashMap_instInhabitedNode___closed__1));
return v___x_199_;
}
}
static size_t _init_l_Lean_PersistentHashMap_shift(void){
_start:
{
size_t v___x_200_; 
v___x_200_ = ((size_t)5ULL);
return v___x_200_;
}
}
static size_t _init_l_Lean_PersistentHashMap_branching(void){
_start:
{
size_t v___x_201_; 
v___x_201_ = ((size_t)32ULL);
return v___x_201_;
}
}
static size_t _init_l_Lean_PersistentHashMap_maxDepth(void){
_start:
{
size_t v___x_202_; 
v___x_202_ = ((size_t)7ULL);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_maxCollisions(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = lean_unsigned_to_nat(4u);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = lean_box(2);
v___x_205_ = lean_unsigned_to_nat(32u);
v___x_206_ = lean_mk_array(v___x_205_, v___x_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object* v_00_u03b1_207_, lean_object* v_00_u03b2_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___closed__0(void){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_210_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___closed__0, &l_Lean_PersistentHashMap_empty___closed__0_once, _init_l_Lean_PersistentHashMap_empty___closed__0);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty(lean_object* v_00_u03b1_213_, lean_object* v_00_u03b2_214_, lean_object* v_inst_215_, lean_object* v_inst_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___closed__1, &l_Lean_PersistentHashMap_empty___closed__1_once, _init_l_Lean_PersistentHashMap_empty___closed__1);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___boxed(lean_object* v_00_u03b1_218_, lean_object* v_00_u03b2_219_, lean_object* v_inst_220_, lean_object* v_inst_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_PersistentHashMap_empty(v_00_u03b1_218_, v_00_u03b2_219_, v_inst_220_, v_inst_221_);
lean_dec_ref(v_inst_221_);
lean_dec_ref(v_inst_220_);
return v_res_222_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___redArg(lean_object* v_x_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___redArg___boxed(lean_object* v_x_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l_Lean_PersistentHashMap_isEmpty___redArg(v_x_225_);
lean_dec_ref(v_x_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty(lean_object* v_00_u03b1_228_, lean_object* v_00_u03b2_229_, lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
uint8_t v___x_233_; 
v___x_233_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___boxed(lean_object* v_00_u03b1_234_, lean_object* v_00_u03b2_235_, lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Lean_PersistentHashMap_isEmpty(v_00_u03b1_234_, v_00_u03b2_235_, v_x_236_, v_x_237_, v_x_238_);
lean_dec_ref(v_x_238_);
lean_dec_ref(v_x_237_);
lean_dec_ref(v_x_236_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object* v_00_u03b1_241_, lean_object* v_00_u03b2_242_, lean_object* v_inst_243_, lean_object* v_inst_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___closed__1, &l_Lean_PersistentHashMap_empty___closed__1_once, _init_l_Lean_PersistentHashMap_empty___closed__1);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___boxed(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_inst_248_, lean_object* v_inst_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_PersistentHashMap_instInhabited(v_00_u03b1_246_, v_00_u03b2_247_, v_inst_248_, v_inst_249_);
lean_dec_ref(v_inst_249_);
lean_dec_ref(v_inst_248_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object* v_00_u03b1_251_, lean_object* v_00_u03b2_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___closed__1, &l_Lean_PersistentHashMap_empty___closed__1_once, _init_l_Lean_PersistentHashMap_empty___closed__1);
return v___x_253_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_mul2Shift(size_t v_i_254_, size_t v_shift_255_){
_start:
{
size_t v___x_256_; 
v___x_256_ = lean_usize_shift_left(v_i_254_, v_shift_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mul2Shift___boxed(lean_object* v_i_257_, lean_object* v_shift_258_){
_start:
{
size_t v_i_boxed_259_; size_t v_shift_boxed_260_; size_t v_res_261_; lean_object* v_r_262_; 
v_i_boxed_259_ = lean_unbox_usize(v_i_257_);
lean_dec(v_i_257_);
v_shift_boxed_260_ = lean_unbox_usize(v_shift_258_);
lean_dec(v_shift_258_);
v_res_261_ = l_Lean_PersistentHashMap_mul2Shift(v_i_boxed_259_, v_shift_boxed_260_);
v_r_262_ = lean_box_usize(v_res_261_);
return v_r_262_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_div2Shift(size_t v_i_263_, size_t v_shift_264_){
_start:
{
size_t v___x_265_; 
v___x_265_ = lean_usize_shift_right(v_i_263_, v_shift_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_div2Shift___boxed(lean_object* v_i_266_, lean_object* v_shift_267_){
_start:
{
size_t v_i_boxed_268_; size_t v_shift_boxed_269_; size_t v_res_270_; lean_object* v_r_271_; 
v_i_boxed_268_ = lean_unbox_usize(v_i_266_);
lean_dec(v_i_266_);
v_shift_boxed_269_ = lean_unbox_usize(v_shift_267_);
lean_dec(v_shift_267_);
v_res_270_ = l_Lean_PersistentHashMap_div2Shift(v_i_boxed_268_, v_shift_boxed_269_);
v_r_271_ = lean_box_usize(v_res_270_);
return v_r_271_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_mod2Shift(size_t v_i_272_, size_t v_shift_273_){
_start:
{
size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; 
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_shift_left(v___x_274_, v_shift_273_);
v___x_276_ = lean_usize_sub(v___x_275_, v___x_274_);
v___x_277_ = lean_usize_land(v_i_272_, v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mod2Shift___boxed(lean_object* v_i_278_, lean_object* v_shift_279_){
_start:
{
size_t v_i_boxed_280_; size_t v_shift_boxed_281_; size_t v_res_282_; lean_object* v_r_283_; 
v_i_boxed_280_ = lean_unbox_usize(v_i_278_);
lean_dec(v_i_278_);
v_shift_boxed_281_ = lean_unbox_usize(v_shift_279_);
lean_dec(v_shift_279_);
v_res_282_ = l_Lean_PersistentHashMap_mod2Shift(v_i_boxed_280_, v_shift_boxed_281_);
v_r_283_ = lean_box_usize(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(lean_object* v_inst_284_, lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
lean_object* v_ks_289_; lean_object* v_vs_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_315_; 
v_ks_289_ = lean_ctor_get(v_x_285_, 0);
v_vs_290_ = lean_ctor_get(v_x_285_, 1);
v_isSharedCheck_315_ = !lean_is_exclusive(v_x_285_);
if (v_isSharedCheck_315_ == 0)
{
v___x_292_ = v_x_285_;
v_isShared_293_ = v_isSharedCheck_315_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_vs_290_);
lean_inc(v_ks_289_);
lean_dec(v_x_285_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_315_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_array_get_size(v_ks_289_);
v___x_295_ = lean_nat_dec_lt(v_x_286_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
lean_dec(v_x_286_);
lean_dec_ref(v_inst_284_);
v___x_296_ = lean_array_push(v_ks_289_, v_x_287_);
v___x_297_ = lean_array_push(v_vs_290_, v_x_288_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v___x_297_);
lean_ctor_set(v___x_292_, 0, v___x_296_);
v___x_299_ = v___x_292_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_296_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
else
{
lean_object* v_k_x27_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_k_x27_301_ = lean_array_fget_borrowed(v_ks_289_, v_x_286_);
lean_inc_ref(v_inst_284_);
lean_inc(v_k_x27_301_);
lean_inc(v_x_287_);
v___x_302_ = lean_apply_2(v_inst_284_, v_x_287_, v_k_x27_301_);
v___x_303_ = lean_unbox(v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_305_; 
if (v_isShared_293_ == 0)
{
v___x_305_ = v___x_292_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_ks_289_);
lean_ctor_set(v_reuseFailAlloc_309_, 1, v_vs_290_);
v___x_305_ = v_reuseFailAlloc_309_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_unsigned_to_nat(1u);
v___x_307_ = lean_nat_add(v_x_286_, v___x_306_);
lean_dec(v_x_286_);
v_x_285_ = v___x_305_;
v_x_286_ = v___x_307_;
goto _start;
}
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec_ref(v_inst_284_);
v___x_310_ = lean_array_fset(v_ks_289_, v_x_286_, v_x_287_);
v___x_311_ = lean_array_fset(v_vs_290_, v_x_286_, v_x_288_);
lean_dec(v_x_286_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v___x_311_);
lean_ctor_set(v___x_292_, 0, v___x_310_);
v___x_313_ = v___x_292_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux(lean_object* v_00_u03b1_316_, lean_object* v_00_u03b2_317_, lean_object* v_inst_318_, lean_object* v_x_319_, lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(v_inst_318_, v_x_319_, v_x_320_, v_x_321_, v_x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(lean_object* v_inst_324_, lean_object* v_n_325_, lean_object* v_k_326_, lean_object* v_v_327_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(v_inst_324_, v_n_325_, v___x_328_, v_k_326_, v_v_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode(lean_object* v_00_u03b1_330_, lean_object* v_00_u03b2_331_, lean_object* v_inst_332_, lean_object* v_n_333_, lean_object* v_k_334_, lean_object* v_v_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(v_inst_332_, v_n_333_, v_k_334_, v_v_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object* v_x_337_){
_start:
{
lean_object* v_ks_338_; lean_object* v___x_339_; 
v_ks_338_ = lean_ctor_get(v_x_337_, 0);
v___x_339_ = lean_array_get_size(v_ks_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg___boxed(lean_object* v_x_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_340_);
lean_dec_ref(v_x_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize(lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_x_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___boxed(lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_x_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lean_PersistentHashMap_getCollisionNodeSize(v_00_u03b1_346_, v_00_u03b2_347_, v_x_348_);
lean_dec_ref(v_x_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object* v_k_u2081_350_, lean_object* v_v_u2081_351_, lean_object* v_k_u2082_352_, lean_object* v_v_u2082_353_){
_start:
{
lean_object* v___x_354_; lean_object* v_ks_355_; lean_object* v___x_356_; lean_object* v_ks_357_; lean_object* v___x_358_; lean_object* v_vs_359_; lean_object* v___x_360_; 
v___x_354_ = lean_unsigned_to_nat(4u);
v_ks_355_ = lean_mk_empty_array_with_capacity(v___x_354_);
lean_inc_ref(v_ks_355_);
v___x_356_ = lean_array_push(v_ks_355_, v_k_u2081_350_);
v_ks_357_ = lean_array_push(v___x_356_, v_k_u2082_352_);
v___x_358_ = lean_array_push(v_ks_355_, v_v_u2081_351_);
v_vs_359_ = lean_array_push(v___x_358_, v_v_u2082_353_);
v___x_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_360_, 0, v_ks_357_);
lean_ctor_set(v___x_360_, 1, v_vs_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode(lean_object* v_00_u03b1_361_, lean_object* v_00_u03b2_362_, lean_object* v_k_u2081_363_, lean_object* v_v_u2081_364_, lean_object* v_k_u2082_365_, lean_object* v_v_u2082_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_k_u2081_363_, v_v_u2081_364_, v_k_u2082_365_, v_v_u2082_366_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__0(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg(lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_x_371_, size_t v_x_372_, size_t v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
lean_object* v_es_376_; size_t v___x_377_; size_t v___x_378_; lean_object* v_j_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
v_es_376_ = lean_ctor_get(v_x_371_, 0);
v___x_377_ = ((size_t)31ULL);
v___x_378_ = lean_usize_land(v_x_372_, v___x_377_);
v_j_379_ = lean_usize_to_nat(v___x_378_);
v___x_380_ = lean_array_get_size(v_es_376_);
v___x_381_ = lean_nat_dec_lt(v_j_379_, v___x_380_);
if (v___x_381_ == 0)
{
lean_dec(v_j_379_);
lean_dec(v_x_375_);
lean_dec(v_x_374_);
lean_dec_ref(v_inst_370_);
lean_dec_ref(v_inst_369_);
return v_x_371_;
}
else
{
lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_421_; 
lean_inc_ref(v_es_376_);
v_isSharedCheck_421_ = !lean_is_exclusive(v_x_371_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v_x_371_, 0);
lean_dec(v_unused_422_);
v___x_383_ = v_x_371_;
v_isShared_384_ = v_isSharedCheck_421_;
goto v_resetjp_382_;
}
else
{
lean_dec(v_x_371_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_421_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v_v_385_; lean_object* v___x_386_; lean_object* v_xs_x27_387_; lean_object* v___y_389_; 
v_v_385_ = lean_array_fget(v_es_376_, v_j_379_);
v___x_386_ = lean_box(0);
v_xs_x27_387_ = lean_array_fset(v_es_376_, v_j_379_, v___x_386_);
switch(lean_obj_tag(v_v_385_))
{
case 0:
{
lean_object* v_key_394_; lean_object* v_val_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref(v_inst_370_);
v_key_394_ = lean_ctor_get(v_v_385_, 0);
v_val_395_ = lean_ctor_get(v_v_385_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_v_385_);
if (v_isSharedCheck_406_ == 0)
{
v___x_397_ = v_v_385_;
v_isShared_398_ = v_isSharedCheck_406_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_val_395_);
lean_inc(v_key_394_);
lean_dec(v_v_385_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_406_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; uint8_t v___x_400_; 
lean_inc(v_key_394_);
lean_inc(v_x_374_);
v___x_399_ = lean_apply_2(v_inst_369_, v_x_374_, v_key_394_);
v___x_400_ = lean_unbox(v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; lean_object* v___x_402_; 
lean_del_object(v___x_397_);
v___x_401_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_394_, v_val_395_, v_x_374_, v_x_375_);
v___x_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
v___y_389_ = v___x_402_;
goto v___jp_388_;
}
else
{
lean_object* v___x_404_; 
lean_dec(v_val_395_);
lean_dec(v_key_394_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 1, v_x_375_);
lean_ctor_set(v___x_397_, 0, v_x_374_);
v___x_404_ = v___x_397_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_x_374_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_x_375_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
v___y_389_ = v___x_404_;
goto v___jp_388_;
}
}
}
}
case 1:
{
lean_object* v_node_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_419_; 
v_node_407_ = lean_ctor_get(v_v_385_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_v_385_);
if (v_isSharedCheck_419_ == 0)
{
v___x_409_ = v_v_385_;
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_node_407_);
lean_dec(v_v_385_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_411_ = ((size_t)5ULL);
v___x_412_ = lean_usize_shift_right(v_x_372_, v___x_411_);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_add(v_x_373_, v___x_413_);
v___x_415_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_369_, v_inst_370_, v_node_407_, v___x_412_, v___x_414_, v_x_374_, v_x_375_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_415_);
v___x_417_ = v___x_409_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
v___y_389_ = v___x_417_;
goto v___jp_388_;
}
}
}
default: 
{
lean_object* v___x_420_; 
lean_dec_ref(v_inst_370_);
lean_dec_ref(v_inst_369_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v_x_374_);
lean_ctor_set(v___x_420_, 1, v_x_375_);
v___y_389_ = v___x_420_;
goto v___jp_388_;
}
}
v___jp_388_:
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = lean_array_fset(v_xs_x27_387_, v_j_379_, v___y_389_);
lean_dec(v_j_379_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v___x_390_);
v___x_392_ = v___x_383_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_390_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
}
else
{
lean_object* v_ks_423_; lean_object* v_vs_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_442_; 
v_ks_423_ = lean_ctor_get(v_x_371_, 0);
v_vs_424_ = lean_ctor_get(v_x_371_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_371_);
if (v_isSharedCheck_442_ == 0)
{
v___x_426_ = v_x_371_;
v_isShared_427_ = v_isSharedCheck_442_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_vs_424_);
lean_inc(v_ks_423_);
lean_dec(v_x_371_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_442_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_ks_423_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_vs_424_);
v___x_429_ = v_reuseFailAlloc_441_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v_newNode_430_; size_t v___x_431_; uint8_t v___x_432_; 
lean_inc_ref(v_inst_369_);
v_newNode_430_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(v_inst_369_, v___x_429_, v_x_374_, v_x_375_);
v___x_431_ = ((size_t)7ULL);
v___x_432_ = lean_usize_dec_le(v___x_431_, v_x_373_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_433_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_430_);
v___x_434_ = lean_unsigned_to_nat(4u);
v___x_435_ = lean_nat_dec_lt(v___x_433_, v___x_434_);
lean_dec(v___x_433_);
if (v___x_435_ == 0)
{
lean_object* v_ks_436_; lean_object* v_vs_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v_ks_436_ = lean_ctor_get(v_newNode_430_, 0);
lean_inc_ref(v_ks_436_);
v_vs_437_ = lean_ctor_get(v_newNode_430_, 1);
lean_inc_ref(v_vs_437_);
lean_dec_ref(v_newNode_430_);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__0);
v___x_440_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_369_, v_inst_370_, v_x_373_, v_ks_436_, v_vs_437_, v___x_438_, v___x_439_);
lean_dec_ref(v_vs_437_);
lean_dec_ref(v_ks_436_);
return v___x_440_;
}
else
{
lean_dec_ref(v_inst_370_);
lean_dec_ref(v_inst_369_);
return v_newNode_430_;
}
}
else
{
lean_dec_ref(v_inst_370_);
lean_dec_ref(v_inst_369_);
return v_newNode_430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(lean_object* v_inst_443_, lean_object* v_inst_444_, size_t v_depth_445_, lean_object* v_keys_446_, lean_object* v_vals_447_, lean_object* v_i_448_, lean_object* v_entries_449_){
_start:
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = lean_array_get_size(v_keys_446_);
v___x_451_ = lean_nat_dec_lt(v_i_448_, v___x_450_);
if (v___x_451_ == 0)
{
lean_dec(v_i_448_);
lean_dec_ref(v_inst_444_);
lean_dec_ref(v_inst_443_);
return v_entries_449_;
}
else
{
lean_object* v_k_452_; lean_object* v_v_453_; lean_object* v___x_454_; uint64_t v___x_455_; size_t v_h_456_; size_t v___x_457_; lean_object* v___x_458_; size_t v___x_459_; size_t v___x_460_; size_t v___x_461_; size_t v_h_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_k_452_ = lean_array_fget_borrowed(v_keys_446_, v_i_448_);
v_v_453_ = lean_array_fget_borrowed(v_vals_447_, v_i_448_);
lean_inc_ref_n(v_inst_444_, 2);
lean_inc_n(v_k_452_, 2);
v___x_454_ = lean_apply_1(v_inst_444_, v_k_452_);
v___x_455_ = lean_unbox_uint64(v___x_454_);
lean_dec_ref(v___x_454_);
v_h_456_ = lean_uint64_to_usize(v___x_455_);
v___x_457_ = ((size_t)5ULL);
v___x_458_ = lean_unsigned_to_nat(1u);
v___x_459_ = ((size_t)1ULL);
v___x_460_ = lean_usize_sub(v_depth_445_, v___x_459_);
v___x_461_ = lean_usize_mul(v___x_457_, v___x_460_);
v_h_462_ = lean_usize_shift_right(v_h_456_, v___x_461_);
v___x_463_ = lean_nat_add(v_i_448_, v___x_458_);
lean_dec(v_i_448_);
lean_inc(v_v_453_);
lean_inc_ref(v_inst_443_);
v___x_464_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_443_, v_inst_444_, v_entries_449_, v_h_462_, v_depth_445_, v_k_452_, v_v_453_);
v_i_448_ = v___x_463_;
v_entries_449_ = v___x_464_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg___boxed(lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_depth_468_, lean_object* v_keys_469_, lean_object* v_vals_470_, lean_object* v_i_471_, lean_object* v_entries_472_){
_start:
{
size_t v_depth_boxed_473_; lean_object* v_res_474_; 
v_depth_boxed_473_ = lean_unbox_usize(v_depth_468_);
lean_dec(v_depth_468_);
v_res_474_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_466_, v_inst_467_, v_depth_boxed_473_, v_keys_469_, v_vals_470_, v_i_471_, v_entries_472_);
lean_dec_ref(v_vals_470_);
lean_dec_ref(v_keys_469_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg___boxed(lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
size_t v_x_391__boxed_482_; size_t v_x_392__boxed_483_; lean_object* v_res_484_; 
v_x_391__boxed_482_ = lean_unbox_usize(v_x_478_);
lean_dec(v_x_478_);
v_x_392__boxed_483_ = lean_unbox_usize(v_x_479_);
lean_dec(v_x_479_);
v_res_484_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_475_, v_inst_476_, v_x_477_, v_x_391__boxed_482_, v_x_392__boxed_483_, v_x_480_, v_x_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, size_t v_depth_489_, lean_object* v_keys_490_, lean_object* v_vals_491_, lean_object* v_heq_492_, lean_object* v_i_493_, lean_object* v_entries_494_){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_487_, v_inst_488_, v_depth_489_, v_keys_490_, v_vals_491_, v_i_493_, v_entries_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___boxed(lean_object* v_00_u03b1_496_, lean_object* v_00_u03b2_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_depth_500_, lean_object* v_keys_501_, lean_object* v_vals_502_, lean_object* v_heq_503_, lean_object* v_i_504_, lean_object* v_entries_505_){
_start:
{
size_t v_depth_boxed_506_; lean_object* v_res_507_; 
v_depth_boxed_506_ = lean_unbox_usize(v_depth_500_);
lean_dec(v_depth_500_);
v_res_507_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(v_00_u03b1_496_, v_00_u03b2_497_, v_inst_498_, v_inst_499_, v_depth_boxed_506_, v_keys_501_, v_vals_502_, v_heq_503_, v_i_504_, v_entries_505_);
lean_dec_ref(v_vals_502_);
lean_dec_ref(v_keys_501_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_x_512_, size_t v_x_513_, size_t v_x_514_, lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_510_, v_inst_511_, v_x_512_, v_x_513_, v_x_514_, v_x_515_, v_x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___boxed(lean_object* v_00_u03b1_518_, lean_object* v_00_u03b2_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_, lean_object* v_x_525_, lean_object* v_x_526_){
_start:
{
size_t v_x_565__boxed_527_; size_t v_x_566__boxed_528_; lean_object* v_res_529_; 
v_x_565__boxed_527_ = lean_unbox_usize(v_x_523_);
lean_dec(v_x_523_);
v_x_566__boxed_528_ = lean_unbox_usize(v_x_524_);
lean_dec(v_x_524_);
v_res_529_ = l_Lean_PersistentHashMap_insertAux(v_00_u03b1_518_, v_00_u03b2_519_, v_inst_520_, v_inst_521_, v_x_522_, v_x_565__boxed_527_, v_x_566__boxed_528_, v_x_525_, v_x_526_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
lean_object* v___x_535_; uint64_t v___x_536_; size_t v___x_537_; size_t v___x_538_; lean_object* v___x_539_; 
lean_inc_ref(v_x_531_);
lean_inc(v_x_533_);
v___x_535_ = lean_apply_1(v_x_531_, v_x_533_);
v___x_536_ = lean_unbox_uint64(v___x_535_);
lean_dec_ref(v___x_535_);
v___x_537_ = lean_uint64_to_usize(v___x_536_);
v___x_538_ = ((size_t)1ULL);
v___x_539_ = l_Lean_PersistentHashMap_insertAux___redArg(v_x_530_, v_x_531_, v_x_532_, v___x_537_, v___x_538_, v_x_533_, v_x_534_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert(lean_object* v_00_u03b1_540_, lean_object* v_00_u03b2_541_, lean_object* v_x_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_PersistentHashMap_insert___redArg(v_x_542_, v_x_543_, v_x_544_, v_x_545_, v_x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg(lean_object* v_inst_548_, lean_object* v_keys_549_, lean_object* v_vals_550_, lean_object* v_i_551_, lean_object* v_k_552_){
_start:
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_array_get_size(v_keys_549_);
v___x_554_ = lean_nat_dec_lt(v_i_551_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
lean_dec(v_k_552_);
lean_dec(v_i_551_);
lean_dec_ref(v_inst_548_);
v___x_555_ = lean_box(0);
return v___x_555_;
}
else
{
lean_object* v_k_x27_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_k_x27_556_ = lean_array_fget_borrowed(v_keys_549_, v_i_551_);
lean_inc_ref(v_inst_548_);
lean_inc(v_k_x27_556_);
lean_inc(v_k_552_);
v___x_557_ = lean_apply_2(v_inst_548_, v_k_552_, v_k_x27_556_);
v___x_558_ = lean_unbox(v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = lean_unsigned_to_nat(1u);
v___x_560_ = lean_nat_add(v_i_551_, v___x_559_);
lean_dec(v_i_551_);
v_i_551_ = v___x_560_;
goto _start;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v_k_552_);
lean_dec_ref(v_inst_548_);
v___x_562_ = lean_array_fget_borrowed(v_vals_550_, v_i_551_);
lean_dec(v_i_551_);
lean_inc(v___x_562_);
v___x_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg___boxed(lean_object* v_inst_564_, lean_object* v_keys_565_, lean_object* v_vals_566_, lean_object* v_i_567_, lean_object* v_k_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_564_, v_keys_565_, v_vals_566_, v_i_567_, v_k_568_);
lean_dec_ref(v_vals_566_);
lean_dec_ref(v_keys_565_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux(lean_object* v_00_u03b1_570_, lean_object* v_00_u03b2_571_, lean_object* v_inst_572_, lean_object* v_keys_573_, lean_object* v_vals_574_, lean_object* v_heq_575_, lean_object* v_i_576_, lean_object* v_k_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_572_, v_keys_573_, v_vals_574_, v_i_576_, v_k_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___boxed(lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_inst_581_, lean_object* v_keys_582_, lean_object* v_vals_583_, lean_object* v_heq_584_, lean_object* v_i_585_, lean_object* v_k_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_PersistentHashMap_findAtAux(v_00_u03b1_579_, v_00_u03b2_580_, v_inst_581_, v_keys_582_, v_vals_583_, v_heq_584_, v_i_585_, v_k_586_);
lean_dec_ref(v_vals_583_);
lean_dec_ref(v_keys_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg(lean_object* v_inst_588_, lean_object* v_x_589_, size_t v_x_590_, lean_object* v_x_591_){
_start:
{
if (lean_obj_tag(v_x_589_) == 0)
{
lean_object* v_es_592_; lean_object* v___x_593_; size_t v___x_594_; size_t v___x_595_; lean_object* v_j_596_; lean_object* v___x_597_; 
v_es_592_ = lean_ctor_get(v_x_589_, 0);
lean_inc_ref(v_es_592_);
lean_dec_ref_known(v_x_589_, 1);
v___x_593_ = lean_box(2);
v___x_594_ = ((size_t)31ULL);
v___x_595_ = lean_usize_land(v_x_590_, v___x_594_);
v_j_596_ = lean_usize_to_nat(v___x_595_);
v___x_597_ = lean_array_get(v___x_593_, v_es_592_, v_j_596_);
lean_dec(v_j_596_);
lean_dec_ref(v_es_592_);
switch(lean_obj_tag(v___x_597_))
{
case 0:
{
lean_object* v_key_598_; lean_object* v_val_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_key_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_key_598_);
v_val_599_ = lean_ctor_get(v___x_597_, 1);
lean_inc(v_val_599_);
lean_dec_ref_known(v___x_597_, 2);
v___x_600_ = lean_apply_2(v_inst_588_, v_x_591_, v_key_598_);
v___x_601_ = lean_unbox(v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; 
lean_dec(v_val_599_);
v___x_602_ = lean_box(0);
return v___x_602_;
}
else
{
lean_object* v___x_603_; 
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v_val_599_);
return v___x_603_;
}
}
case 1:
{
lean_object* v_node_604_; size_t v___x_605_; size_t v___x_606_; 
v_node_604_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_node_604_);
lean_dec_ref_known(v___x_597_, 1);
v___x_605_ = ((size_t)5ULL);
v___x_606_ = lean_usize_shift_right(v_x_590_, v___x_605_);
v_x_589_ = v_node_604_;
v_x_590_ = v___x_606_;
goto _start;
}
default: 
{
lean_object* v___x_608_; 
lean_dec(v_x_591_);
lean_dec_ref(v_inst_588_);
v___x_608_ = lean_box(0);
return v___x_608_;
}
}
}
else
{
lean_object* v_ks_609_; lean_object* v_vs_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_ks_609_ = lean_ctor_get(v_x_589_, 0);
lean_inc_ref(v_ks_609_);
v_vs_610_ = lean_ctor_get(v_x_589_, 1);
lean_inc_ref(v_vs_610_);
lean_dec_ref_known(v_x_589_, 2);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_588_, v_ks_609_, v_vs_610_, v___x_611_, v_x_591_);
lean_dec_ref(v_vs_610_);
lean_dec_ref(v_ks_609_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg___boxed(lean_object* v_inst_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_x_616_){
_start:
{
size_t v_x_117__boxed_617_; lean_object* v_res_618_; 
v_x_117__boxed_617_ = lean_unbox_usize(v_x_615_);
lean_dec(v_x_615_);
v_res_618_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_613_, v_x_614_, v_x_117__boxed_617_, v_x_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux(lean_object* v_00_u03b1_619_, lean_object* v_00_u03b2_620_, lean_object* v_inst_621_, lean_object* v_x_622_, size_t v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v___x_625_; 
lean_inc_ref(v_x_622_);
v___x_625_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_621_, v_x_622_, v_x_623_, v_x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___boxed(lean_object* v_00_u03b1_626_, lean_object* v_00_u03b2_627_, lean_object* v_inst_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
size_t v_x_169__boxed_632_; lean_object* v_res_633_; 
v_x_169__boxed_632_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_res_633_ = l_Lean_PersistentHashMap_findAux(v_00_u03b1_626_, v_00_u03b2_627_, v_inst_628_, v_x_629_, v_x_169__boxed_632_, v_x_631_);
lean_dec_ref(v_x_629_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
lean_object* v___x_638_; uint64_t v___x_639_; size_t v___x_640_; lean_object* v___x_641_; 
lean_inc(v_x_637_);
v___x_638_ = lean_apply_1(v_x_635_, v_x_637_);
v___x_639_ = lean_unbox_uint64(v___x_638_);
lean_dec_ref(v___x_638_);
v___x_640_ = lean_uint64_to_usize(v___x_639_);
lean_inc_ref(v_x_636_);
v___x_641_ = l_Lean_PersistentHashMap_findAux___redArg(v_x_634_, v_x_636_, v___x_640_, v_x_637_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg___boxed(lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_642_, v_x_643_, v_x_644_, v_x_645_);
lean_dec_ref(v_x_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f(lean_object* v_00_u03b1_647_, lean_object* v_00_u03b2_648_, lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_649_, v_x_650_, v_x_651_, v_x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___boxed(lean_object* v_00_u03b1_654_, lean_object* v_00_u03b2_655_, lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_PersistentHashMap_find_x3f(v_00_u03b1_654_, v_00_u03b2_655_, v_x_656_, v_x_657_, v_x_658_, v_x_659_);
lean_dec_ref(v_x_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_m_663_, lean_object* v_i_664_, lean_object* v_x_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_661_, v_x_662_, v_m_663_, v_i_664_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed(lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_m_669_, lean_object* v_i_670_, lean_object* v_x_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(v_x_667_, v_x_668_, v_m_669_, v_i_670_, v_x_671_);
lean_dec_ref(v_m_669_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg(lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
lean_object* v___f_675_; 
v___f_675_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_675_, 0, v_x_673_);
lean_closure_set(v___f_675_, 1, v_x_674_);
return v___f_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
lean_object* v___f_680_; 
v___f_680_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_680_, 0, v_x_678_);
lean_closure_set(v___f_680_, 1, v_x_679_);
return v___f_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg(lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_m_683_, lean_object* v_a_684_, lean_object* v_b_u2080_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_681_, v_x_682_, v_m_683_, v_a_684_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_inc(v_b_u2080_685_);
return v_b_u2080_685_;
}
else
{
lean_object* v_val_687_; 
v_val_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v___x_686_, 1);
return v_val_687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg___boxed(lean_object* v_x_688_, lean_object* v_x_689_, lean_object* v_m_690_, lean_object* v_a_691_, lean_object* v_b_u2080_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_PersistentHashMap_findD___redArg(v_x_688_, v_x_689_, v_m_690_, v_a_691_, v_b_u2080_692_);
lean_dec(v_b_u2080_692_);
lean_dec_ref(v_m_690_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD(lean_object* v_00_u03b1_694_, lean_object* v_00_u03b2_695_, lean_object* v_x_696_, lean_object* v_x_697_, lean_object* v_m_698_, lean_object* v_a_699_, lean_object* v_b_u2080_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_696_, v_x_697_, v_m_698_, v_a_699_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_inc(v_b_u2080_700_);
return v_b_u2080_700_;
}
else
{
lean_object* v_val_702_; 
v_val_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v___x_701_, 1);
return v_val_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___boxed(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_m_707_, lean_object* v_a_708_, lean_object* v_b_u2080_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_PersistentHashMap_findD(v_00_u03b1_703_, v_00_u03b2_704_, v_x_705_, v_x_706_, v_m_707_, v_a_708_, v_b_u2080_709_);
lean_dec(v_b_u2080_709_);
lean_dec_ref(v_m_707_);
return v_res_710_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_714_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__2));
v___x_715_ = lean_unsigned_to_nat(14u);
v___x_716_ = lean_unsigned_to_nat(178u);
v___x_717_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__1));
v___x_718_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__0));
v___x_719_ = l_mkPanicMessageWithDecl(v___x_718_, v___x_717_, v___x_716_, v___x_715_, v___x_714_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg(lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_inst_722_, lean_object* v_m_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_720_, v_x_721_, v_m_723_, v_a_724_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_727_ = l_panic___redArg(v_inst_722_, v___x_726_);
return v___x_727_;
}
else
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v___x_725_, 1);
return v_val_728_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg___boxed(lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_inst_731_, lean_object* v_m_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_PersistentHashMap_find_x21___redArg(v_x_729_, v_x_730_, v_inst_731_, v_m_732_, v_a_733_);
lean_dec_ref(v_m_732_);
lean_dec(v_inst_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21(lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_inst_739_, lean_object* v_m_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_737_, v_x_738_, v_m_740_, v_a_741_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_744_ = l_panic___redArg(v_inst_739_, v___x_743_);
return v___x_744_;
}
else
{
lean_object* v_val_745_; 
v_val_745_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_val_745_);
lean_dec_ref_known(v___x_742_, 1);
return v_val_745_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___boxed(lean_object* v_00_u03b1_746_, lean_object* v_00_u03b2_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_inst_750_, lean_object* v_m_751_, lean_object* v_a_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_PersistentHashMap_find_x21(v_00_u03b1_746_, v_00_u03b2_747_, v_x_748_, v_x_749_, v_inst_750_, v_m_751_, v_a_752_);
lean_dec_ref(v_m_751_);
lean_dec(v_inst_750_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg(lean_object* v_inst_754_, lean_object* v_keys_755_, lean_object* v_vals_756_, lean_object* v_i_757_, lean_object* v_k_758_){
_start:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_array_get_size(v_keys_755_);
v___x_760_ = lean_nat_dec_lt(v_i_757_, v___x_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
lean_dec(v_k_758_);
lean_dec(v_i_757_);
lean_dec_ref(v_inst_754_);
v___x_761_ = lean_box(0);
return v___x_761_;
}
else
{
lean_object* v_k_x27_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_k_x27_762_ = lean_array_fget_borrowed(v_keys_755_, v_i_757_);
lean_inc_ref(v_inst_754_);
lean_inc(v_k_x27_762_);
lean_inc(v_k_758_);
v___x_763_ = lean_apply_2(v_inst_754_, v_k_758_, v_k_x27_762_);
v___x_764_ = lean_unbox(v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_nat_add(v_i_757_, v___x_765_);
lean_dec(v_i_757_);
v_i_757_ = v___x_766_;
goto _start;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
lean_dec(v_k_758_);
lean_dec_ref(v_inst_754_);
v___x_768_ = lean_array_fget_borrowed(v_vals_756_, v_i_757_);
lean_dec(v_i_757_);
lean_inc(v___x_768_);
lean_inc(v_k_x27_762_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v_k_x27_762_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg___boxed(lean_object* v_inst_771_, lean_object* v_keys_772_, lean_object* v_vals_773_, lean_object* v_i_774_, lean_object* v_k_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_771_, v_keys_772_, v_vals_773_, v_i_774_, v_k_775_);
lean_dec_ref(v_vals_773_);
lean_dec_ref(v_keys_772_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux(lean_object* v_00_u03b1_777_, lean_object* v_00_u03b2_778_, lean_object* v_inst_779_, lean_object* v_keys_780_, lean_object* v_vals_781_, lean_object* v_heq_782_, lean_object* v_i_783_, lean_object* v_k_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_779_, v_keys_780_, v_vals_781_, v_i_783_, v_k_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___boxed(lean_object* v_00_u03b1_786_, lean_object* v_00_u03b2_787_, lean_object* v_inst_788_, lean_object* v_keys_789_, lean_object* v_vals_790_, lean_object* v_heq_791_, lean_object* v_i_792_, lean_object* v_k_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_PersistentHashMap_findEntryAtAux(v_00_u03b1_786_, v_00_u03b2_787_, v_inst_788_, v_keys_789_, v_vals_790_, v_heq_791_, v_i_792_, v_k_793_);
lean_dec_ref(v_vals_790_);
lean_dec_ref(v_keys_789_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg(lean_object* v_inst_795_, lean_object* v_x_796_, size_t v_x_797_, lean_object* v_x_798_){
_start:
{
if (lean_obj_tag(v_x_796_) == 0)
{
lean_object* v_es_799_; lean_object* v___x_800_; size_t v___x_801_; size_t v___x_802_; lean_object* v_j_803_; lean_object* v___x_804_; 
v_es_799_ = lean_ctor_get(v_x_796_, 0);
lean_inc_ref(v_es_799_);
lean_dec_ref_known(v_x_796_, 1);
v___x_800_ = lean_box(2);
v___x_801_ = ((size_t)31ULL);
v___x_802_ = lean_usize_land(v_x_797_, v___x_801_);
v_j_803_ = lean_usize_to_nat(v___x_802_);
v___x_804_ = lean_array_get(v___x_800_, v_es_799_, v_j_803_);
lean_dec(v_j_803_);
lean_dec_ref(v_es_799_);
switch(lean_obj_tag(v___x_804_))
{
case 0:
{
lean_object* v_key_805_; lean_object* v_val_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_key_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc_n(v_key_805_, 2);
v_val_806_ = lean_ctor_get(v___x_804_, 1);
lean_inc(v_val_806_);
lean_dec_ref_known(v___x_804_, 2);
v___x_807_ = lean_apply_2(v_inst_795_, v_x_798_, v_key_805_);
v___x_808_ = lean_unbox(v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v_val_806_);
lean_dec(v_key_805_);
v___x_809_ = lean_box(0);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v_key_805_);
lean_ctor_set(v___x_810_, 1, v_val_806_);
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
}
case 1:
{
lean_object* v_node_812_; size_t v___x_813_; size_t v___x_814_; 
v_node_812_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_node_812_);
lean_dec_ref_known(v___x_804_, 1);
v___x_813_ = ((size_t)5ULL);
v___x_814_ = lean_usize_shift_right(v_x_797_, v___x_813_);
v_x_796_ = v_node_812_;
v_x_797_ = v___x_814_;
goto _start;
}
default: 
{
lean_object* v___x_816_; 
lean_dec(v_x_798_);
lean_dec_ref(v_inst_795_);
v___x_816_ = lean_box(0);
return v___x_816_;
}
}
}
else
{
lean_object* v_ks_817_; lean_object* v_vs_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v_ks_817_ = lean_ctor_get(v_x_796_, 0);
lean_inc_ref(v_ks_817_);
v_vs_818_ = lean_ctor_get(v_x_796_, 1);
lean_inc_ref(v_vs_818_);
lean_dec_ref_known(v_x_796_, 2);
v___x_819_ = lean_unsigned_to_nat(0u);
v___x_820_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_795_, v_ks_817_, v_vs_818_, v___x_819_, v_x_798_);
lean_dec_ref(v_vs_818_);
lean_dec_ref(v_ks_817_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg___boxed(lean_object* v_inst_821_, lean_object* v_x_822_, lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
size_t v_x_120__boxed_825_; lean_object* v_res_826_; 
v_x_120__boxed_825_ = lean_unbox_usize(v_x_823_);
lean_dec(v_x_823_);
v_res_826_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_821_, v_x_822_, v_x_120__boxed_825_, v_x_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux(lean_object* v_00_u03b1_827_, lean_object* v_00_u03b2_828_, lean_object* v_inst_829_, lean_object* v_x_830_, size_t v_x_831_, lean_object* v_x_832_){
_start:
{
lean_object* v___x_833_; 
lean_inc_ref(v_x_830_);
v___x_833_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_829_, v_x_830_, v_x_831_, v_x_832_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___boxed(lean_object* v_00_u03b1_834_, lean_object* v_00_u03b2_835_, lean_object* v_inst_836_, lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
size_t v_x_174__boxed_840_; lean_object* v_res_841_; 
v_x_174__boxed_840_ = lean_unbox_usize(v_x_838_);
lean_dec(v_x_838_);
v_res_841_ = l_Lean_PersistentHashMap_findEntryAux(v_00_u03b1_834_, v_00_u03b2_835_, v_inst_836_, v_x_837_, v_x_174__boxed_840_, v_x_839_);
lean_dec_ref(v_x_837_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_x_844_, lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; uint64_t v___x_847_; size_t v___x_848_; lean_object* v___x_849_; 
lean_inc(v_x_845_);
v___x_846_ = lean_apply_1(v_x_843_, v_x_845_);
v___x_847_ = lean_unbox_uint64(v___x_846_);
lean_dec_ref(v___x_846_);
v___x_848_ = lean_uint64_to_usize(v___x_847_);
lean_inc_ref(v_x_844_);
v___x_849_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_x_842_, v_x_844_, v___x_848_, v_x_845_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg___boxed(lean_object* v_x_850_, lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_850_, v_x_851_, v_x_852_, v_x_853_);
lean_dec_ref(v_x_852_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f(lean_object* v_00_u03b1_855_, lean_object* v_00_u03b2_856_, lean_object* v_x_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_857_, v_x_858_, v_x_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___boxed(lean_object* v_00_u03b1_862_, lean_object* v_00_u03b2_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_, lean_object* v_x_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_PersistentHashMap_findEntry_x3f(v_00_u03b1_862_, v_00_u03b2_863_, v_x_864_, v_x_865_, v_x_866_, v_x_867_);
lean_dec_ref(v_x_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg(lean_object* v_inst_869_, lean_object* v_keys_870_, lean_object* v_i_871_, lean_object* v_k_872_, lean_object* v_k_u2080_873_){
_start:
{
lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_874_ = lean_array_get_size(v_keys_870_);
v___x_875_ = lean_nat_dec_lt(v_i_871_, v___x_874_);
if (v___x_875_ == 0)
{
lean_dec(v_k_872_);
lean_dec(v_i_871_);
lean_dec_ref(v_inst_869_);
lean_inc(v_k_u2080_873_);
return v_k_u2080_873_;
}
else
{
lean_object* v_k_x27_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v_k_x27_876_ = lean_array_fget_borrowed(v_keys_870_, v_i_871_);
lean_inc_ref(v_inst_869_);
lean_inc(v_k_x27_876_);
lean_inc(v_k_872_);
v___x_877_ = lean_apply_2(v_inst_869_, v_k_872_, v_k_x27_876_);
v___x_878_ = lean_unbox(v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = lean_nat_add(v_i_871_, v___x_879_);
lean_dec(v_i_871_);
v_i_871_ = v___x_880_;
goto _start;
}
else
{
lean_dec(v_k_872_);
lean_dec(v_i_871_);
lean_dec_ref(v_inst_869_);
lean_inc(v_k_x27_876_);
return v_k_x27_876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg___boxed(lean_object* v_inst_882_, lean_object* v_keys_883_, lean_object* v_i_884_, lean_object* v_k_885_, lean_object* v_k_u2080_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_882_, v_keys_883_, v_i_884_, v_k_885_, v_k_u2080_886_);
lean_dec(v_k_u2080_886_);
lean_dec_ref(v_keys_883_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux(lean_object* v_00_u03b1_888_, lean_object* v_00_u03b2_889_, lean_object* v_inst_890_, lean_object* v_keys_891_, lean_object* v_vals_892_, lean_object* v_heq_893_, lean_object* v_i_894_, lean_object* v_k_895_, lean_object* v_k_u2080_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_890_, v_keys_891_, v_i_894_, v_k_895_, v_k_u2080_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___boxed(lean_object* v_00_u03b1_898_, lean_object* v_00_u03b2_899_, lean_object* v_inst_900_, lean_object* v_keys_901_, lean_object* v_vals_902_, lean_object* v_heq_903_, lean_object* v_i_904_, lean_object* v_k_905_, lean_object* v_k_u2080_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_PersistentHashMap_findKeyDAtAux(v_00_u03b1_898_, v_00_u03b2_899_, v_inst_900_, v_keys_901_, v_vals_902_, v_heq_903_, v_i_904_, v_k_905_, v_k_u2080_906_);
lean_dec(v_k_u2080_906_);
lean_dec_ref(v_vals_902_);
lean_dec_ref(v_keys_901_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object* v_inst_908_, lean_object* v_x_909_, size_t v_x_910_, lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
if (lean_obj_tag(v_x_909_) == 0)
{
lean_object* v_es_913_; lean_object* v___x_914_; size_t v___x_915_; size_t v___x_916_; lean_object* v_j_917_; lean_object* v___x_918_; 
v_es_913_ = lean_ctor_get(v_x_909_, 0);
lean_inc_ref(v_es_913_);
lean_dec_ref_known(v_x_909_, 1);
v___x_914_ = lean_box(2);
v___x_915_ = ((size_t)31ULL);
v___x_916_ = lean_usize_land(v_x_910_, v___x_915_);
v_j_917_ = lean_usize_to_nat(v___x_916_);
v___x_918_ = lean_array_get(v___x_914_, v_es_913_, v_j_917_);
lean_dec(v_j_917_);
lean_dec_ref(v_es_913_);
switch(lean_obj_tag(v___x_918_))
{
case 0:
{
lean_object* v_key_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_key_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc_n(v_key_919_, 2);
lean_dec_ref_known(v___x_918_, 2);
v___x_920_ = lean_apply_2(v_inst_908_, v_x_911_, v_key_919_);
v___x_921_ = lean_unbox(v___x_920_);
if (v___x_921_ == 0)
{
lean_dec(v_key_919_);
lean_inc(v_x_912_);
return v_x_912_;
}
else
{
return v_key_919_;
}
}
case 1:
{
lean_object* v_node_922_; size_t v___x_923_; size_t v___x_924_; 
v_node_922_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_node_922_);
lean_dec_ref_known(v___x_918_, 1);
v___x_923_ = ((size_t)5ULL);
v___x_924_ = lean_usize_shift_right(v_x_910_, v___x_923_);
v_x_909_ = v_node_922_;
v_x_910_ = v___x_924_;
goto _start;
}
default: 
{
lean_dec(v_x_911_);
lean_dec_ref(v_inst_908_);
lean_inc(v_x_912_);
return v_x_912_;
}
}
}
else
{
lean_object* v_ks_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_ks_926_ = lean_ctor_get(v_x_909_, 0);
lean_inc_ref(v_ks_926_);
lean_dec_ref_known(v_x_909_, 2);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_908_, v_ks_926_, v___x_927_, v_x_911_, v_x_912_);
lean_dec_ref(v_ks_926_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg___boxed(lean_object* v_inst_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
size_t v_x_112__boxed_934_; lean_object* v_res_935_; 
v_x_112__boxed_934_ = lean_unbox_usize(v_x_931_);
lean_dec(v_x_931_);
v_res_935_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_929_, v_x_930_, v_x_112__boxed_934_, v_x_932_, v_x_933_);
lean_dec(v_x_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux(lean_object* v_00_u03b1_936_, lean_object* v_00_u03b2_937_, lean_object* v_inst_938_, lean_object* v_x_939_, size_t v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_938_, v_x_939_, v_x_940_, v_x_941_, v_x_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___boxed(lean_object* v_00_u03b1_944_, lean_object* v_00_u03b2_945_, lean_object* v_inst_946_, lean_object* v_x_947_, lean_object* v_x_948_, lean_object* v_x_949_, lean_object* v_x_950_){
_start:
{
size_t v_x_159__boxed_951_; lean_object* v_res_952_; 
v_x_159__boxed_951_ = lean_unbox_usize(v_x_948_);
lean_dec(v_x_948_);
v_res_952_ = l_Lean_PersistentHashMap_findKeyDAux(v_00_u03b1_944_, v_00_u03b2_945_, v_inst_946_, v_x_947_, v_x_159__boxed_951_, v_x_949_, v_x_950_);
lean_dec(v_x_950_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg(lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_m_955_, lean_object* v_a_956_, lean_object* v_a_u2080_957_){
_start:
{
lean_object* v___x_958_; uint64_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; 
lean_inc(v_a_956_);
v___x_958_ = lean_apply_1(v_x_954_, v_a_956_);
v___x_959_ = lean_unbox_uint64(v___x_958_);
lean_dec_ref(v___x_958_);
v___x_960_ = lean_uint64_to_usize(v___x_959_);
v___x_961_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_953_, v_m_955_, v___x_960_, v_a_956_, v_a_u2080_957_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg___boxed(lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_m_964_, lean_object* v_a_965_, lean_object* v_a_u2080_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_PersistentHashMap_findKeyD___redArg(v_x_962_, v_x_963_, v_m_964_, v_a_965_, v_a_u2080_966_);
lean_dec(v_a_u2080_966_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD(lean_object* v_00_u03b1_968_, lean_object* v_00_u03b2_969_, lean_object* v_x_970_, lean_object* v_x_971_, lean_object* v_m_972_, lean_object* v_a_973_, lean_object* v_a_u2080_974_){
_start:
{
lean_object* v___x_975_; uint64_t v___x_976_; size_t v___x_977_; lean_object* v___x_978_; 
lean_inc(v_a_973_);
v___x_975_ = lean_apply_1(v_x_971_, v_a_973_);
v___x_976_ = lean_unbox_uint64(v___x_975_);
lean_dec_ref(v___x_975_);
v___x_977_ = lean_uint64_to_usize(v___x_976_);
v___x_978_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_970_, v_m_972_, v___x_977_, v_a_973_, v_a_u2080_974_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___boxed(lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_m_983_, lean_object* v_a_984_, lean_object* v_a_u2080_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_PersistentHashMap_findKeyD(v_00_u03b1_979_, v_00_u03b2_980_, v_x_981_, v_x_982_, v_m_983_, v_a_984_, v_a_u2080_985_);
lean_dec(v_a_u2080_985_);
return v_res_986_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___redArg(lean_object* v_inst_987_, lean_object* v_keys_988_, lean_object* v_i_989_, lean_object* v_k_990_){
_start:
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_array_get_size(v_keys_988_);
v___x_992_ = lean_nat_dec_lt(v_i_989_, v___x_991_);
if (v___x_992_ == 0)
{
lean_dec(v_k_990_);
lean_dec(v_i_989_);
lean_dec_ref(v_inst_987_);
return v___x_992_;
}
else
{
lean_object* v_k_x27_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_k_x27_993_ = lean_array_fget_borrowed(v_keys_988_, v_i_989_);
lean_inc_ref(v_inst_987_);
lean_inc(v_k_x27_993_);
lean_inc(v_k_990_);
v___x_994_ = lean_apply_2(v_inst_987_, v_k_990_, v_k_x27_993_);
v___x_995_ = lean_unbox(v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_unsigned_to_nat(1u);
v___x_997_ = lean_nat_add(v_i_989_, v___x_996_);
lean_dec(v_i_989_);
v_i_989_ = v___x_997_;
goto _start;
}
else
{
lean_dec(v_k_990_);
lean_dec(v_i_989_);
lean_dec_ref(v_inst_987_);
return v___x_992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___redArg___boxed(lean_object* v_inst_999_, lean_object* v_keys_1000_, lean_object* v_i_1001_, lean_object* v_k_1002_){
_start:
{
uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_res_1003_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_999_, v_keys_1000_, v_i_1001_, v_k_1002_);
lean_dec_ref(v_keys_1000_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux(lean_object* v_00_u03b1_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_inst_1007_, lean_object* v_keys_1008_, lean_object* v_vals_1009_, lean_object* v_heq_1010_, lean_object* v_i_1011_, lean_object* v_k_1012_){
_start:
{
uint8_t v___x_1013_; 
v___x_1013_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1007_, v_keys_1008_, v_i_1011_, v_k_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___boxed(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_inst_1016_, lean_object* v_keys_1017_, lean_object* v_vals_1018_, lean_object* v_heq_1019_, lean_object* v_i_1020_, lean_object* v_k_1021_){
_start:
{
uint8_t v_res_1022_; lean_object* v_r_1023_; 
v_res_1022_ = l_Lean_PersistentHashMap_containsAtAux(v_00_u03b1_1014_, v_00_u03b2_1015_, v_inst_1016_, v_keys_1017_, v_vals_1018_, v_heq_1019_, v_i_1020_, v_k_1021_);
lean_dec_ref(v_vals_1018_);
lean_dec_ref(v_keys_1017_);
v_r_1023_ = lean_box(v_res_1022_);
return v_r_1023_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___redArg(lean_object* v_inst_1024_, lean_object* v_x_1025_, size_t v_x_1026_, lean_object* v_x_1027_){
_start:
{
if (lean_obj_tag(v_x_1025_) == 0)
{
lean_object* v_es_1028_; lean_object* v___x_1029_; size_t v___x_1030_; size_t v___x_1031_; lean_object* v_j_1032_; lean_object* v___x_1033_; 
v_es_1028_ = lean_ctor_get(v_x_1025_, 0);
lean_inc_ref(v_es_1028_);
lean_dec_ref_known(v_x_1025_, 1);
v___x_1029_ = lean_box(2);
v___x_1030_ = ((size_t)31ULL);
v___x_1031_ = lean_usize_land(v_x_1026_, v___x_1030_);
v_j_1032_ = lean_usize_to_nat(v___x_1031_);
v___x_1033_ = lean_array_get(v___x_1029_, v_es_1028_, v_j_1032_);
lean_dec(v_j_1032_);
lean_dec_ref(v_es_1028_);
switch(lean_obj_tag(v___x_1033_))
{
case 0:
{
lean_object* v_key_1034_; lean_object* v___x_1035_; uint8_t v___x_1036_; 
v_key_1034_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_key_1034_);
lean_dec_ref_known(v___x_1033_, 2);
v___x_1035_ = lean_apply_2(v_inst_1024_, v_x_1027_, v_key_1034_);
v___x_1036_ = lean_unbox(v___x_1035_);
return v___x_1036_;
}
case 1:
{
lean_object* v_node_1037_; size_t v___x_1038_; size_t v___x_1039_; 
v_node_1037_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_node_1037_);
lean_dec_ref_known(v___x_1033_, 1);
v___x_1038_ = ((size_t)5ULL);
v___x_1039_ = lean_usize_shift_right(v_x_1026_, v___x_1038_);
v_x_1025_ = v_node_1037_;
v_x_1026_ = v___x_1039_;
goto _start;
}
default: 
{
uint8_t v___x_1041_; 
lean_dec(v_x_1027_);
lean_dec_ref(v_inst_1024_);
v___x_1041_ = 0;
return v___x_1041_;
}
}
}
else
{
lean_object* v_ks_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_ks_1042_ = lean_ctor_get(v_x_1025_, 0);
lean_inc_ref(v_ks_1042_);
lean_dec_ref_known(v_x_1025_, 2);
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1024_, v_ks_1042_, v___x_1043_, v_x_1027_);
lean_dec_ref(v_ks_1042_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___redArg___boxed(lean_object* v_inst_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
size_t v_x_103__boxed_1049_; uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_x_103__boxed_1049_ = lean_unbox_usize(v_x_1047_);
lean_dec(v_x_1047_);
v_res_1050_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1045_, v_x_1046_, v_x_103__boxed_1049_, v_x_1048_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux(lean_object* v_00_u03b1_1052_, lean_object* v_00_u03b2_1053_, lean_object* v_inst_1054_, lean_object* v_x_1055_, size_t v_x_1056_, lean_object* v_x_1057_){
_start:
{
uint8_t v___x_1058_; 
v___x_1058_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1054_, v_x_1055_, v_x_1056_, v_x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___boxed(lean_object* v_00_u03b1_1059_, lean_object* v_00_u03b2_1060_, lean_object* v_inst_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
size_t v_x_149__boxed_1065_; uint8_t v_res_1066_; lean_object* v_r_1067_; 
v_x_149__boxed_1065_ = lean_unbox_usize(v_x_1063_);
lean_dec(v_x_1063_);
v_res_1066_ = l_Lean_PersistentHashMap_containsAux(v_00_u03b1_1059_, v_00_u03b2_1060_, v_inst_1061_, v_x_1062_, v_x_149__boxed_1065_, v_x_1064_);
v_r_1067_ = lean_box(v_res_1066_);
return v_r_1067_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v___x_1072_; uint64_t v___x_1073_; size_t v___x_1074_; uint8_t v___x_1075_; 
lean_inc(v_x_1071_);
v___x_1072_ = lean_apply_1(v_inst_1069_, v_x_1071_);
v___x_1073_ = lean_unbox_uint64(v___x_1072_);
lean_dec_ref(v___x_1072_);
v___x_1074_ = lean_uint64_to_usize(v___x_1073_);
v___x_1075_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1068_, v_x_1070_, v___x_1074_, v_x_1071_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___redArg___boxed(lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
uint8_t v_res_1080_; lean_object* v_r_1081_; 
v_res_1080_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1076_, v_inst_1077_, v_x_1078_, v_x_1079_);
v_r_1081_ = lean_box(v_res_1080_);
return v_r_1081_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains(lean_object* v_00_u03b1_1082_, lean_object* v_00_u03b2_1083_, lean_object* v_inst_1084_, lean_object* v_inst_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
uint8_t v___x_1088_; 
v___x_1088_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1084_, v_inst_1085_, v_x_1086_, v_x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___boxed(lean_object* v_00_u03b1_1089_, lean_object* v_00_u03b2_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
uint8_t v_res_1095_; lean_object* v_r_1096_; 
v_res_1095_ = l_Lean_PersistentHashMap_contains(v_00_u03b1_1089_, v_00_u03b2_1090_, v_inst_1091_, v_inst_1092_, v_x_1093_, v_x_1094_);
v_r_1096_ = lean_box(v_res_1095_);
return v_r_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg(lean_object* v_a_1097_, lean_object* v_i_1098_, lean_object* v_acc_1099_){
_start:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = lean_array_get_size(v_a_1097_);
v___x_1101_ = lean_nat_dec_lt(v_i_1098_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_dec(v_i_1098_);
return v_acc_1099_;
}
else
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_array_fget(v_a_1097_, v_i_1098_);
switch(lean_obj_tag(v___x_1102_))
{
case 0:
{
if (lean_obj_tag(v_acc_1099_) == 0)
{
lean_object* v_key_1103_; lean_object* v_val_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1115_; 
v_key_1103_ = lean_ctor_get(v___x_1102_, 0);
v_val_1104_ = lean_ctor_get(v___x_1102_, 1);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1106_ = v___x_1102_;
v_isShared_1107_ = v_isSharedCheck_1115_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_val_1104_);
lean_inc(v_key_1103_);
lean_dec(v___x_1102_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1115_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1108_ = lean_unsigned_to_nat(1u);
v___x_1109_ = lean_nat_add(v_i_1098_, v___x_1108_);
lean_dec(v_i_1098_);
if (v_isShared_1107_ == 0)
{
v___x_1111_ = v___x_1106_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_key_1103_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_val_1104_);
v___x_1111_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
v_i_1098_ = v___x_1109_;
v_acc_1099_ = v___x_1112_;
goto _start;
}
}
}
else
{
lean_object* v___x_1116_; 
lean_dec_ref_known(v_acc_1099_, 1);
lean_dec_ref_known(v___x_1102_, 2);
lean_dec(v_i_1098_);
v___x_1116_ = lean_box(0);
return v___x_1116_;
}
}
case 1:
{
lean_object* v___x_1117_; 
lean_dec_ref_known(v___x_1102_, 1);
lean_dec(v_acc_1099_);
lean_dec(v_i_1098_);
v___x_1117_ = lean_box(0);
return v___x_1117_;
}
default: 
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_nat_add(v_i_1098_, v___x_1118_);
lean_dec(v_i_1098_);
v_i_1098_ = v___x_1119_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg___boxed(lean_object* v_a_1121_, lean_object* v_i_1122_, lean_object* v_acc_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1121_, v_i_1122_, v_acc_1123_);
lean_dec_ref(v_a_1121_);
return v_res_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_a_1127_, lean_object* v_i_1128_, lean_object* v_acc_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1127_, v_i_1128_, v_acc_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___boxed(lean_object* v_00_u03b1_1131_, lean_object* v_00_u03b2_1132_, lean_object* v_a_1133_, lean_object* v_i_1134_, lean_object* v_acc_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_PersistentHashMap_isUnaryEntries(v_00_u03b1_1131_, v_00_u03b2_1132_, v_a_1133_, v_i_1134_, v_acc_1135_);
lean_dec_ref(v_a_1133_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object* v_x_1137_){
_start:
{
if (lean_obj_tag(v_x_1137_) == 0)
{
lean_object* v_es_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_es_1138_ = lean_ctor_get(v_x_1137_, 0);
lean_inc_ref(v_es_1138_);
lean_dec_ref_known(v_x_1137_, 1);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = lean_box(0);
v___x_1141_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_es_1138_, v___x_1139_, v___x_1140_);
lean_dec_ref(v_es_1138_);
return v___x_1141_;
}
else
{
lean_object* v_ks_1142_; lean_object* v_vs_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1158_; 
v_ks_1142_ = lean_ctor_get(v_x_1137_, 0);
v_vs_1143_ = lean_ctor_get(v_x_1137_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_x_1137_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1145_ = v_x_1137_;
v_isShared_1146_ = v_isSharedCheck_1158_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_vs_1143_);
lean_inc(v_ks_1142_);
lean_dec(v_x_1137_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1158_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1147_ = lean_unsigned_to_nat(1u);
v___x_1148_ = lean_array_get_size(v_ks_1142_);
v___x_1149_ = lean_nat_dec_eq(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_del_object(v___x_1145_);
lean_dec_ref(v_vs_1143_);
lean_dec_ref(v_ks_1142_);
v___x_1150_ = lean_box(0);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1151_ = lean_unsigned_to_nat(0u);
v___x_1152_ = lean_array_fget(v_ks_1142_, v___x_1151_);
lean_dec_ref(v_ks_1142_);
v___x_1153_ = lean_array_fget(v_vs_1143_, v___x_1151_);
lean_dec_ref(v_vs_1143_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 0);
lean_ctor_set(v___x_1145_, 1, v___x_1153_);
lean_ctor_set(v___x_1145_, 0, v___x_1152_);
v___x_1155_ = v___x_1145_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1152_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode(lean_object* v_00_u03b1_1159_, lean_object* v_00_u03b2_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg(lean_object* v_inst_1163_, lean_object* v_x_1164_, size_t v_x_1165_, lean_object* v_x_1166_){
_start:
{
if (lean_obj_tag(v_x_1164_) == 0)
{
lean_object* v_es_1167_; lean_object* v___x_1168_; size_t v___x_1169_; size_t v___x_1170_; lean_object* v_j_1171_; lean_object* v_entry_1172_; 
v_es_1167_ = lean_ctor_get(v_x_1164_, 0);
v___x_1168_ = lean_box(2);
v___x_1169_ = ((size_t)31ULL);
v___x_1170_ = lean_usize_land(v_x_1165_, v___x_1169_);
v_j_1171_ = lean_usize_to_nat(v___x_1170_);
v_entry_1172_ = lean_array_get(v___x_1168_, v_es_1167_, v_j_1171_);
switch(lean_obj_tag(v_entry_1172_))
{
case 0:
{
lean_object* v_key_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v_key_1173_ = lean_ctor_get(v_entry_1172_, 0);
lean_inc(v_key_1173_);
lean_dec_ref_known(v_entry_1172_, 2);
v___x_1174_ = lean_apply_2(v_inst_1163_, v_x_1166_, v_key_1173_);
v___x_1175_ = lean_unbox(v___x_1174_);
if (v___x_1175_ == 0)
{
lean_dec(v_j_1171_);
return v_x_1164_;
}
else
{
lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
lean_inc_ref(v_es_1167_);
v_isSharedCheck_1183_ = !lean_is_exclusive(v_x_1164_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; 
v_unused_1184_ = lean_ctor_get(v_x_1164_, 0);
lean_dec(v_unused_1184_);
v___x_1177_ = v_x_1164_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_dec(v_x_1164_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_array_set(v_es_1167_, v_j_1171_, v___x_1168_);
lean_dec(v_j_1171_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 0, v___x_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
case 1:
{
lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1219_; 
lean_inc_ref(v_es_1167_);
v_isSharedCheck_1219_ = !lean_is_exclusive(v_x_1164_);
if (v_isSharedCheck_1219_ == 0)
{
lean_object* v_unused_1220_; 
v_unused_1220_ = lean_ctor_get(v_x_1164_, 0);
lean_dec(v_unused_1220_);
v___x_1186_ = v_x_1164_;
v_isShared_1187_ = v_isSharedCheck_1219_;
goto v_resetjp_1185_;
}
else
{
lean_dec(v_x_1164_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1219_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_node_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1218_; 
v_node_1188_ = lean_ctor_get(v_entry_1172_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_entry_1172_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1190_ = v_entry_1172_;
v_isShared_1191_ = v_isSharedCheck_1218_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_node_1188_);
lean_dec(v_entry_1172_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1218_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
size_t v___x_1192_; lean_object* v_entries_1193_; size_t v___x_1194_; lean_object* v_newNode_1195_; lean_object* v___x_1196_; 
v___x_1192_ = ((size_t)5ULL);
v_entries_1193_ = lean_array_set(v_es_1167_, v_j_1171_, v___x_1168_);
v___x_1194_ = lean_usize_shift_right(v_x_1165_, v___x_1192_);
v_newNode_1195_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1163_, v_node_1188_, v___x_1194_, v_x_1166_);
lean_inc_ref(v_newNode_1195_);
v___x_1196_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1195_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v___x_1198_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v_newNode_1195_);
v___x_1198_ = v___x_1190_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_newNode_1195_);
v___x_1198_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = lean_array_set(v_entries_1193_, v_j_1171_, v___x_1198_);
lean_dec(v_j_1171_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1199_);
v___x_1201_ = v___x_1186_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
else
{
lean_object* v_val_1204_; lean_object* v_fst_1205_; lean_object* v_snd_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_newNode_1195_);
lean_del_object(v___x_1190_);
v_val_1204_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_val_1204_);
lean_dec_ref_known(v___x_1196_, 1);
v_fst_1205_ = lean_ctor_get(v_val_1204_, 0);
v_snd_1206_ = lean_ctor_get(v_val_1204_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_val_1204_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1208_ = v_val_1204_;
v_isShared_1209_ = v_isSharedCheck_1217_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_snd_1206_);
lean_inc(v_fst_1205_);
lean_dec(v_val_1204_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1217_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_fst_1205_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_snd_1206_);
v___x_1211_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = lean_array_set(v_entries_1193_, v_j_1171_, v___x_1211_);
lean_dec(v_j_1171_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1212_);
v___x_1214_ = v___x_1186_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1171_);
lean_dec(v_x_1166_);
lean_dec_ref(v_inst_1163_);
return v_x_1164_;
}
}
}
else
{
lean_object* v_ks_1221_; lean_object* v_vs_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1236_; 
v_ks_1221_ = lean_ctor_get(v_x_1164_, 0);
v_vs_1222_ = lean_ctor_get(v_x_1164_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_x_1164_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1224_ = v_x_1164_;
v_isShared_1225_ = v_isSharedCheck_1236_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_vs_1222_);
lean_inc(v_ks_1221_);
lean_dec(v_x_1164_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1236_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Array_finIdxOf_x3f___redArg(v_inst_1163_, v_ks_1221_, v_x_1166_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v___x_1228_; 
if (v_isShared_1225_ == 0)
{
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_ks_1221_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_vs_1222_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
else
{
lean_object* v_val_1230_; lean_object* v_keys_x27_1231_; lean_object* v_vals_x27_1232_; lean_object* v___x_1234_; 
v_val_1230_ = lean_ctor_get(v___x_1226_, 0);
lean_inc_n(v_val_1230_, 2);
lean_dec_ref_known(v___x_1226_, 1);
v_keys_x27_1231_ = l_Array_eraseIdx___redArg(v_ks_1221_, v_val_1230_);
v_vals_x27_1232_ = l_Array_eraseIdx___redArg(v_vs_1222_, v_val_1230_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 1, v_vals_x27_1232_);
lean_ctor_set(v___x_1224_, 0, v_keys_x27_1231_);
v___x_1234_ = v___x_1224_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_keys_x27_1231_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_vals_x27_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg___boxed(lean_object* v_inst_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_, lean_object* v_x_1240_){
_start:
{
size_t v_x_198__boxed_1241_; lean_object* v_res_1242_; 
v_x_198__boxed_1241_ = lean_unbox_usize(v_x_1239_);
lean_dec(v_x_1239_);
v_res_1242_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1237_, v_x_1238_, v_x_198__boxed_1241_, v_x_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux(lean_object* v_00_u03b1_1243_, lean_object* v_00_u03b2_1244_, lean_object* v_inst_1245_, lean_object* v_x_1246_, size_t v_x_1247_, lean_object* v_x_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1245_, v_x_1246_, v_x_1247_, v_x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___boxed(lean_object* v_00_u03b1_1250_, lean_object* v_00_u03b2_1251_, lean_object* v_inst_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
size_t v_x_339__boxed_1256_; lean_object* v_res_1257_; 
v_x_339__boxed_1256_ = lean_unbox_usize(v_x_1254_);
lean_dec(v_x_1254_);
v_res_1257_ = l_Lean_PersistentHashMap_eraseAux(v_00_u03b1_1250_, v_00_u03b2_1251_, v_inst_1252_, v_x_1253_, v_x_339__boxed_1256_, v_x_1255_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object* v_x_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
lean_object* v___x_1262_; uint64_t v___x_1263_; size_t v_h_1264_; lean_object* v___x_1265_; 
lean_inc(v_x_1261_);
v___x_1262_ = lean_apply_1(v_x_1259_, v_x_1261_);
v___x_1263_ = lean_unbox_uint64(v___x_1262_);
lean_dec_ref(v___x_1262_);
v_h_1264_ = lean_uint64_to_usize(v___x_1263_);
v___x_1265_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_x_1258_, v_x_1260_, v_h_1264_, v_x_1261_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase(lean_object* v_00_u03b1_1266_, lean_object* v_00_u03b2_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_PersistentHashMap_erase___redArg(v_x_1268_, v_x_1269_, v_x_1270_, v_x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg(lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_f_1275_, lean_object* v_x_1276_, size_t v_x_1277_, size_t v_x_1278_, lean_object* v_x_1279_){
_start:
{
if (lean_obj_tag(v_x_1276_) == 0)
{
lean_object* v_es_1280_; size_t v___x_1281_; size_t v___x_1282_; lean_object* v_j_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_es_1280_ = lean_ctor_get(v_x_1276_, 0);
v___x_1281_ = ((size_t)31ULL);
v___x_1282_ = lean_usize_land(v_x_1277_, v___x_1281_);
v_j_1283_ = lean_usize_to_nat(v___x_1282_);
v___x_1284_ = lean_array_get_size(v_es_1280_);
v___x_1285_ = lean_nat_dec_lt(v_j_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_dec(v_j_1283_);
lean_dec(v_x_1279_);
lean_dec_ref(v_f_1275_);
lean_dec_ref(v_inst_1274_);
lean_dec_ref(v_inst_1273_);
return v_x_1276_;
}
else
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1354_; 
lean_inc_ref(v_es_1280_);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_x_1276_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v_x_1276_, 0);
lean_dec(v_unused_1355_);
v___x_1287_ = v_x_1276_;
v_isShared_1288_ = v_isSharedCheck_1354_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v_x_1276_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1354_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_v_1289_; lean_object* v___x_1290_; lean_object* v_xs_x27_1291_; lean_object* v___y_1293_; 
v_v_1289_ = lean_array_fget(v_es_1280_, v_j_1283_);
v___x_1290_ = lean_box(0);
v_xs_x27_1291_ = lean_array_fset(v_es_1280_, v_j_1283_, v___x_1290_);
switch(lean_obj_tag(v_v_1289_))
{
case 0:
{
lean_object* v_key_1298_; lean_object* v_val_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
lean_dec_ref(v_inst_1274_);
v_key_1298_ = lean_ctor_get(v_v_1289_, 0);
v_val_1299_ = lean_ctor_get(v_v_1289_, 1);
lean_inc(v_key_1298_);
lean_inc(v_x_1279_);
v___x_1300_ = lean_apply_2(v_inst_1273_, v_x_1279_, v_key_1298_);
v___x_1301_ = lean_unbox(v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_apply_1(v_f_1275_, v___x_1302_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_dec(v_x_1279_);
v___y_1293_ = v_v_1289_;
goto v___jp_1292_;
}
else
{
lean_object* v_val_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1312_; 
lean_inc(v_val_1299_);
lean_inc(v_key_1298_);
lean_dec_ref_known(v_v_1289_, 2);
v_val_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_val_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1312_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
v___x_1308_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1298_, v_val_1299_, v_x_1279_, v_val_1304_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v___x_1308_);
v___x_1310_ = v___x_1306_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
v___y_1293_ = v___x_1310_;
goto v___jp_1292_;
}
}
}
}
else
{
lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1323_; 
lean_inc(v_val_1299_);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_v_1289_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; lean_object* v_unused_1325_; 
v_unused_1324_ = lean_ctor_get(v_v_1289_, 1);
lean_dec(v_unused_1324_);
v_unused_1325_ = lean_ctor_get(v_v_1289_, 0);
lean_dec(v_unused_1325_);
v___x_1314_ = v_v_1289_;
v_isShared_1315_ = v_isSharedCheck_1323_;
goto v_resetjp_1313_;
}
else
{
lean_dec(v_v_1289_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1323_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_val_1299_);
v___x_1317_ = lean_apply_1(v_f_1275_, v___x_1316_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v___x_1318_; 
lean_del_object(v___x_1314_);
lean_dec(v_x_1279_);
v___x_1318_ = lean_box(2);
v___y_1293_ = v___x_1318_;
goto v___jp_1292_;
}
else
{
lean_object* v_val_1319_; lean_object* v___x_1321_; 
v_val_1319_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_val_1319_);
lean_dec_ref_known(v___x_1317_, 1);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 1, v_val_1319_);
lean_ctor_set(v___x_1314_, 0, v_x_1279_);
v___x_1321_ = v___x_1314_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_x_1279_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_val_1319_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
v___y_1293_ = v___x_1321_;
goto v___jp_1292_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1349_; 
v_node_1326_ = lean_ctor_get(v_v_1289_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_v_1289_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1328_ = v_v_1289_;
v_isShared_1329_ = v_isSharedCheck_1349_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_node_1326_);
lean_dec(v_v_1289_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1349_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
size_t v___x_1330_; size_t v___x_1331_; size_t v___x_1332_; size_t v___x_1333_; lean_object* v_newNode_1334_; lean_object* v___x_1335_; 
v___x_1330_ = ((size_t)5ULL);
v___x_1331_ = lean_usize_shift_right(v_x_1277_, v___x_1330_);
v___x_1332_ = ((size_t)1ULL);
v___x_1333_ = lean_usize_add(v_x_1278_, v___x_1332_);
v_newNode_1334_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1273_, v_inst_1274_, v_f_1275_, v_node_1326_, v___x_1331_, v___x_1333_, v_x_1279_);
lean_inc_ref(v_newNode_1334_);
v___x_1335_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1334_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v___x_1337_; 
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 0, v_newNode_1334_);
v___x_1337_ = v___x_1328_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_newNode_1334_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
v___y_1293_ = v___x_1337_;
goto v___jp_1292_;
}
}
else
{
lean_object* v_val_1339_; lean_object* v_fst_1340_; lean_object* v_snd_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_newNode_1334_);
lean_del_object(v___x_1328_);
v_val_1339_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_val_1339_);
lean_dec_ref_known(v___x_1335_, 1);
v_fst_1340_ = lean_ctor_get(v_val_1339_, 0);
v_snd_1341_ = lean_ctor_get(v_val_1339_, 1);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_val_1339_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v_val_1339_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_snd_1341_);
lean_inc(v_fst_1340_);
lean_dec(v_val_1339_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_fst_1340_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_snd_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
v___y_1293_ = v___x_1346_;
goto v___jp_1292_;
}
}
}
}
}
default: 
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec_ref(v_inst_1274_);
lean_dec_ref(v_inst_1273_);
v___x_1350_ = lean_box(0);
v___x_1351_ = lean_apply_1(v_f_1275_, v___x_1350_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_dec(v_x_1279_);
v___y_1293_ = v_v_1289_;
goto v___jp_1292_;
}
else
{
lean_object* v_val_1352_; lean_object* v___x_1353_; 
v_val_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_val_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_x_1279_);
lean_ctor_set(v___x_1353_, 1, v_val_1352_);
v___y_1293_ = v___x_1353_;
goto v___jp_1292_;
}
}
}
v___jp_1292_:
{
lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1294_ = lean_array_fset(v_xs_x27_1291_, v_j_1283_, v___y_1293_);
lean_dec(v_j_1283_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1294_);
v___x_1296_ = v___x_1287_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
else
{
lean_object* v_ks_1356_; lean_object* v_vs_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1390_; 
v_ks_1356_ = lean_ctor_get(v_x_1276_, 0);
v_vs_1357_ = lean_ctor_get(v_x_1276_, 1);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_x_1276_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1359_ = v_x_1276_;
v_isShared_1360_ = v_isSharedCheck_1390_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_vs_1357_);
lean_inc(v_ks_1356_);
lean_dec(v_x_1276_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1390_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; 
lean_inc(v_x_1279_);
lean_inc_ref(v_inst_1273_);
v___x_1361_ = l_Array_finIdxOf_x3f___redArg(v_inst_1273_, v_ks_1356_, v_x_1279_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v___x_1363_; 
if (v_isShared_1360_ == 0)
{
v___x_1363_ = v___x_1359_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_ks_1356_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_vs_1357_);
v___x_1363_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_apply_1(v_f_1275_, v___x_1364_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_dec(v_x_1279_);
lean_dec_ref(v_inst_1274_);
lean_dec_ref(v_inst_1273_);
return v___x_1363_;
}
else
{
lean_object* v_val_1366_; lean_object* v___x_1367_; 
v_val_1366_ = lean_ctor_get(v___x_1365_, 0);
lean_inc(v_val_1366_);
lean_dec_ref_known(v___x_1365_, 1);
v___x_1367_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_1273_, v_inst_1274_, v___x_1363_, v_x_1277_, v_x_1278_, v_x_1279_, v_val_1366_);
return v___x_1367_;
}
}
}
else
{
lean_object* v_val_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1389_; 
lean_dec_ref(v_inst_1274_);
lean_dec_ref(v_inst_1273_);
v_val_1369_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1371_ = v___x_1361_;
v_isShared_1372_ = v_isSharedCheck_1389_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_val_1369_);
lean_dec(v___x_1361_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1389_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v_v_x27_1373_; lean_object* v_keys_1374_; lean_object* v_vals_1375_; lean_object* v___x_1377_; 
v_v_x27_1373_ = lean_array_fget(v_vs_1357_, v_val_1369_);
lean_inc(v_val_1369_);
v_keys_1374_ = l_Array_eraseIdx___redArg(v_ks_1356_, v_val_1369_);
v_vals_1375_ = l_Array_eraseIdx___redArg(v_vs_1357_, v_val_1369_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v_v_x27_1373_);
v___x_1377_ = v___x_1371_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_v_x27_1373_);
v___x_1377_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_apply_1(v_f_1275_, v___x_1377_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v___x_1380_; 
lean_dec(v_x_1279_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v_vals_1375_);
lean_ctor_set(v___x_1359_, 0, v_keys_1374_);
v___x_1380_ = v___x_1359_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_keys_1374_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_vals_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_object* v_val_1382_; lean_object* v_keys_1383_; lean_object* v_vals_1384_; lean_object* v___x_1386_; 
v_val_1382_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_val_1382_);
lean_dec_ref_known(v___x_1378_, 1);
v_keys_1383_ = lean_array_push(v_keys_1374_, v_x_1279_);
v_vals_1384_ = lean_array_push(v_vals_1375_, v_val_1382_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v_vals_1384_);
lean_ctor_set(v___x_1359_, 0, v_keys_1383_);
v___x_1386_ = v___x_1359_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_keys_1383_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_vals_1384_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg___boxed(lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_f_1393_, lean_object* v_x_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_){
_start:
{
size_t v_x_407__boxed_1398_; size_t v_x_408__boxed_1399_; lean_object* v_res_1400_; 
v_x_407__boxed_1398_ = lean_unbox_usize(v_x_1395_);
lean_dec(v_x_1395_);
v_x_408__boxed_1399_ = lean_unbox_usize(v_x_1396_);
lean_dec(v_x_1396_);
v_res_1400_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1391_, v_inst_1392_, v_f_1393_, v_x_1394_, v_x_407__boxed_1398_, v_x_408__boxed_1399_, v_x_1397_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux(lean_object* v_00_u03b1_1401_, lean_object* v_00_u03b2_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_f_1405_, lean_object* v_x_1406_, size_t v_x_1407_, size_t v_x_1408_, lean_object* v_x_1409_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1403_, v_inst_1404_, v_f_1405_, v_x_1406_, v_x_1407_, v_x_1408_, v_x_1409_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___boxed(lean_object* v_00_u03b1_1411_, lean_object* v_00_u03b2_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_f_1415_, lean_object* v_x_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_, lean_object* v_x_1419_){
_start:
{
size_t v_x_629__boxed_1420_; size_t v_x_630__boxed_1421_; lean_object* v_res_1422_; 
v_x_629__boxed_1420_ = lean_unbox_usize(v_x_1417_);
lean_dec(v_x_1417_);
v_x_630__boxed_1421_ = lean_unbox_usize(v_x_1418_);
lean_dec(v_x_1418_);
v_res_1422_ = l_Lean_PersistentHashMap_alterAux(v_00_u03b1_1411_, v_00_u03b2_1412_, v_inst_1413_, v_inst_1414_, v_f_1415_, v_x_1416_, v_x_629__boxed_1420_, v_x_630__boxed_1421_, v_x_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter___redArg(lean_object* v_x_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_){
_start:
{
lean_object* v___x_1428_; uint64_t v___x_1429_; size_t v_h_1430_; size_t v___x_1431_; lean_object* v___x_1432_; 
lean_inc_ref(v_x_1424_);
lean_inc(v_x_1426_);
v___x_1428_ = lean_apply_1(v_x_1424_, v_x_1426_);
v___x_1429_ = lean_unbox_uint64(v___x_1428_);
lean_dec_ref(v___x_1428_);
v_h_1430_ = lean_uint64_to_usize(v___x_1429_);
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1423_, v_x_1424_, v_x_1427_, v_x_1425_, v_h_1430_, v___x_1431_, v_x_1426_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter(lean_object* v_00_u03b1_1433_, lean_object* v_00_u03b2_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_){
_start:
{
lean_object* v___x_1440_; uint64_t v___x_1441_; size_t v_h_1442_; size_t v___x_1443_; lean_object* v___x_1444_; 
lean_inc_ref(v_x_1436_);
lean_inc(v_x_1438_);
v___x_1440_ = lean_apply_1(v_x_1436_, v_x_1438_);
v___x_1441_ = lean_unbox_uint64(v___x_1440_);
lean_dec_ref(v___x_1440_);
v_h_1442_ = lean_uint64_to_usize(v___x_1441_);
v___x_1443_ = ((size_t)1ULL);
v___x_1444_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1435_, v_x_1436_, v_x_1439_, v_x_1437_, v_h_1442_, v___x_1443_, v_x_1438_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed(lean_object* v_i_1445_, lean_object* v_inst_1446_, lean_object* v_f_1447_, lean_object* v_keys_1448_, lean_object* v_vals_1449_, lean_object* v_____do__lift_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(v_i_1445_, v_inst_1446_, v_f_1447_, v_keys_1448_, v_vals_1449_, v_____do__lift_1450_);
lean_dec(v_i_1445_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(lean_object* v_inst_1452_, lean_object* v_f_1453_, lean_object* v_keys_1454_, lean_object* v_vals_1455_, lean_object* v_i_1456_, lean_object* v_acc_1457_){
_start:
{
lean_object* v_toApplicative_1458_; lean_object* v_toBind_1459_; lean_object* v_toPure_1460_; lean_object* v___x_1461_; uint8_t v___x_1462_; 
v_toApplicative_1458_ = lean_ctor_get(v_inst_1452_, 0);
v_toBind_1459_ = lean_ctor_get(v_inst_1452_, 1);
lean_inc(v_toBind_1459_);
v_toPure_1460_ = lean_ctor_get(v_toApplicative_1458_, 1);
v___x_1461_ = lean_array_get_size(v_keys_1454_);
v___x_1462_ = lean_nat_dec_lt(v_i_1456_, v___x_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; 
lean_inc(v_toPure_1460_);
lean_dec(v_toBind_1459_);
lean_dec(v_i_1456_);
lean_dec_ref(v_vals_1455_);
lean_dec_ref(v_keys_1454_);
lean_dec(v_f_1453_);
lean_dec_ref(v_inst_1452_);
v___x_1463_ = lean_apply_2(v_toPure_1460_, lean_box(0), v_acc_1457_);
return v___x_1463_;
}
else
{
lean_object* v___f_1464_; lean_object* v_k_1465_; lean_object* v_v_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_inc_ref(v_vals_1455_);
lean_inc_ref(v_keys_1454_);
lean_inc(v_f_1453_);
lean_inc(v_i_1456_);
v___f_1464_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1464_, 0, v_i_1456_);
lean_closure_set(v___f_1464_, 1, v_inst_1452_);
lean_closure_set(v___f_1464_, 2, v_f_1453_);
lean_closure_set(v___f_1464_, 3, v_keys_1454_);
lean_closure_set(v___f_1464_, 4, v_vals_1455_);
v_k_1465_ = lean_array_fget(v_keys_1454_, v_i_1456_);
lean_dec_ref(v_keys_1454_);
v_v_1466_ = lean_array_fget(v_vals_1455_, v_i_1456_);
lean_dec(v_i_1456_);
lean_dec_ref(v_vals_1455_);
v___x_1467_ = lean_apply_3(v_f_1453_, v_acc_1457_, v_k_1465_, v_v_1466_);
v___x_1468_ = lean_apply_4(v_toBind_1459_, lean_box(0), lean_box(0), v___x_1467_, v___f_1464_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(lean_object* v_i_1469_, lean_object* v_inst_1470_, lean_object* v_f_1471_, lean_object* v_keys_1472_, lean_object* v_vals_1473_, lean_object* v_____do__lift_1474_){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1475_ = lean_unsigned_to_nat(1u);
v___x_1476_ = lean_nat_add(v_i_1469_, v___x_1475_);
v___x_1477_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1470_, v_f_1471_, v_keys_1472_, v_vals_1473_, v___x_1476_, v_____do__lift_1474_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse(lean_object* v_m_1478_, lean_object* v_inst_1479_, lean_object* v_00_u03c3_1480_, lean_object* v_00_u03b1_1481_, lean_object* v_00_u03b2_1482_, lean_object* v_f_1483_, lean_object* v_keys_1484_, lean_object* v_vals_1485_, lean_object* v_heq_1486_, lean_object* v_i_1487_, lean_object* v_acc_1488_){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1479_, v_f_1483_, v_keys_1484_, v_vals_1485_, v_i_1487_, v_acc_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object* v_inst_1490_, lean_object* v_f_1491_, lean_object* v_x_1492_, lean_object* v_x_1493_){
_start:
{
if (lean_obj_tag(v_x_1492_) == 0)
{
lean_object* v_toApplicative_1494_; lean_object* v_toPure_1495_; lean_object* v_es_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v_toApplicative_1494_ = lean_ctor_get(v_inst_1490_, 0);
v_toPure_1495_ = lean_ctor_get(v_toApplicative_1494_, 1);
v_es_1496_ = lean_ctor_get(v_x_1492_, 0);
lean_inc_ref(v_es_1496_);
lean_dec_ref_known(v_x_1492_, 1);
v___x_1497_ = lean_unsigned_to_nat(0u);
v___x_1498_ = lean_array_get_size(v_es_1496_);
v___x_1499_ = lean_nat_dec_lt(v___x_1497_, v___x_1498_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; 
lean_inc(v_toPure_1495_);
lean_dec_ref(v_es_1496_);
lean_dec(v_f_1491_);
lean_dec_ref(v_inst_1490_);
v___x_1500_ = lean_apply_2(v_toPure_1495_, lean_box(0), v_x_1493_);
return v___x_1500_;
}
else
{
lean_object* v___f_1501_; uint8_t v___x_1502_; 
lean_inc(v_toPure_1495_);
lean_inc_ref(v_inst_1490_);
v___f_1501_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1501_, 0, v_f_1491_);
lean_closure_set(v___f_1501_, 1, v_inst_1490_);
lean_closure_set(v___f_1501_, 2, v_toPure_1495_);
v___x_1502_ = lean_nat_dec_le(v___x_1498_, v___x_1498_);
if (v___x_1502_ == 0)
{
if (v___x_1499_ == 0)
{
lean_object* v___x_1503_; 
lean_inc(v_toPure_1495_);
lean_dec_ref(v___f_1501_);
lean_dec_ref(v_es_1496_);
lean_dec_ref(v_inst_1490_);
v___x_1503_ = lean_apply_2(v_toPure_1495_, lean_box(0), v_x_1493_);
return v___x_1503_;
}
else
{
size_t v___x_1504_; size_t v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = ((size_t)0ULL);
v___x_1505_ = lean_usize_of_nat(v___x_1498_);
v___x_1506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1490_, v___f_1501_, v_es_1496_, v___x_1504_, v___x_1505_, v_x_1493_);
return v___x_1506_;
}
}
else
{
size_t v___x_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = ((size_t)0ULL);
v___x_1508_ = lean_usize_of_nat(v___x_1498_);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1490_, v___f_1501_, v_es_1496_, v___x_1507_, v___x_1508_, v_x_1493_);
return v___x_1509_;
}
}
}
else
{
lean_object* v_ks_1510_; lean_object* v_vs_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v_ks_1510_ = lean_ctor_get(v_x_1492_, 0);
lean_inc_ref(v_ks_1510_);
v_vs_1511_ = lean_ctor_get(v_x_1492_, 1);
lean_inc_ref(v_vs_1511_);
lean_dec_ref_known(v_x_1492_, 2);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1490_, v_f_1491_, v_ks_1510_, v_vs_1511_, v___x_1512_, v_x_1493_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0(lean_object* v_f_1514_, lean_object* v_inst_1515_, lean_object* v_toPure_1516_, lean_object* v_acc_1517_, lean_object* v_entry_1518_){
_start:
{
switch(lean_obj_tag(v_entry_1518_))
{
case 0:
{
lean_object* v_key_1519_; lean_object* v_val_1520_; lean_object* v___x_1521_; 
lean_dec(v_toPure_1516_);
lean_dec_ref(v_inst_1515_);
v_key_1519_ = lean_ctor_get(v_entry_1518_, 0);
lean_inc(v_key_1519_);
v_val_1520_ = lean_ctor_get(v_entry_1518_, 1);
lean_inc(v_val_1520_);
lean_dec_ref_known(v_entry_1518_, 2);
v___x_1521_ = lean_apply_3(v_f_1514_, v_acc_1517_, v_key_1519_, v_val_1520_);
return v___x_1521_;
}
case 1:
{
lean_object* v_node_1522_; lean_object* v___x_1523_; 
lean_dec(v_toPure_1516_);
v_node_1522_ = lean_ctor_get(v_entry_1518_, 0);
lean_inc(v_node_1522_);
lean_dec_ref_known(v_entry_1518_, 1);
v___x_1523_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1515_, v_f_1514_, v_node_1522_, v_acc_1517_);
return v___x_1523_;
}
default: 
{
lean_object* v___x_1524_; 
lean_dec_ref(v_inst_1515_);
lean_dec(v_f_1514_);
v___x_1524_ = lean_apply_2(v_toPure_1516_, lean_box(0), v_acc_1517_);
return v___x_1524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux(lean_object* v_m_1525_, lean_object* v_inst_1526_, lean_object* v_00_u03c3_1527_, lean_object* v_00_u03b1_1528_, lean_object* v_00_u03b2_1529_, lean_object* v_f_1530_, lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1526_, v_f_1530_, v_x_1531_, v_x_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___redArg(lean_object* v_inst_1534_, lean_object* v_map_1535_, lean_object* v_f_1536_, lean_object* v_init_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1534_, v_f_1536_, v_map_1535_, v_init_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM(lean_object* v_m_1539_, lean_object* v_inst_1540_, lean_object* v_00_u03c3_1541_, lean_object* v_00_u03b1_1542_, lean_object* v_00_u03b2_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_map_1546_, lean_object* v_f_1547_, lean_object* v_init_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1540_, v_f_1547_, v_map_1546_, v_init_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___boxed(lean_object* v_m_1550_, lean_object* v_inst_1551_, lean_object* v_00_u03c3_1552_, lean_object* v_00_u03b1_1553_, lean_object* v_00_u03b2_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_, lean_object* v_map_1557_, lean_object* v_f_1558_, lean_object* v_init_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Lean_PersistentHashMap_foldlM(v_m_1550_, v_inst_1551_, v_00_u03c3_1552_, v_00_u03b1_1553_, v_00_u03b2_1554_, v_x_1555_, v_x_1556_, v_map_1557_, v_f_1558_, v_init_1559_);
lean_dec_ref(v_x_1556_);
lean_dec_ref(v_x_1555_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg___lam__0(lean_object* v_f_1561_, lean_object* v_x_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_apply_2(v_f_1561_, v___y_1563_, v___y_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg(lean_object* v_inst_1566_, lean_object* v_map_1567_, lean_object* v_f_1568_){
_start:
{
lean_object* v___f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___f_1569_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1569_, 0, v_f_1568_);
v___x_1570_ = lean_box(0);
v___x_1571_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1566_, v___f_1569_, v_map_1567_, v___x_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM(lean_object* v_m_1572_, lean_object* v_inst_1573_, lean_object* v_00_u03b1_1574_, lean_object* v_00_u03b2_1575_, lean_object* v_x_1576_, lean_object* v_x_1577_, lean_object* v_map_1578_, lean_object* v_f_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_1573_, v_map_1578_, v_f_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___boxed(lean_object* v_m_1581_, lean_object* v_inst_1582_, lean_object* v_00_u03b1_1583_, lean_object* v_00_u03b2_1584_, lean_object* v_x_1585_, lean_object* v_x_1586_, lean_object* v_map_1587_, lean_object* v_f_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_PersistentHashMap_forM(v_m_1581_, v_inst_1582_, v_00_u03b1_1583_, v_00_u03b2_1584_, v_x_1585_, v_x_1586_, v_map_1587_, v_f_1588_);
lean_dec_ref(v_x_1586_);
lean_dec_ref(v_x_1585_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg___lam__0(lean_object* v_f_1590_, lean_object* v_x1_1591_, lean_object* v_x2_1592_, lean_object* v_x3_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_apply_3(v_f_1590_, v_x1_1591_, v_x2_1592_, v_x3_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object* v_map_1614_, lean_object* v_f_1615_, lean_object* v_init_1616_){
_start:
{
lean_object* v___f_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___f_1617_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1617_, 0, v_f_1615_);
v___x_1618_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1619_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1618_, v___f_1617_, v_map_1614_, v_init_1616_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl(lean_object* v_00_u03c3_1620_, lean_object* v_00_u03b1_1621_, lean_object* v_00_u03b2_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_, lean_object* v_map_1625_, lean_object* v_f_1626_, lean_object* v_init_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_1625_, v_f_1626_, v_init_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___boxed(lean_object* v_00_u03c3_1629_, lean_object* v_00_u03b1_1630_, lean_object* v_00_u03b2_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_, lean_object* v_map_1634_, lean_object* v_f_1635_, lean_object* v_init_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Lean_PersistentHashMap_foldl(v_00_u03c3_1629_, v_00_u03b1_1630_, v_00_u03b2_1631_, v_x_1632_, v_x_1633_, v_map_1634_, v_f_1635_, v_init_1636_);
lean_dec_ref(v_x_1633_);
lean_dec_ref(v_x_1632_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__0(lean_object* v_x_1638_){
_start:
{
if (lean_obj_tag(v_x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
v_a_1639_ = lean_ctor_get(v_x_1638_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_x_1638_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v_x_1638_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v_x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
else
{
lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1654_; 
v_a_1647_ = lean_ctor_get(v_x_1638_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v_x_1638_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1649_ = v_x_1638_;
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v_x_1638_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1654_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1652_; 
if (v_isShared_1650_ == 0)
{
v___x_1652_ = v___x_1649_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1647_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__1(lean_object* v_toPure_1655_, lean_object* v_result_1656_){
_start:
{
lean_object* v_a_1657_; lean_object* v___x_1658_; 
v_a_1657_ = lean_ctor_get(v_result_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref(v_result_1656_);
v___x_1658_ = lean_apply_2(v_toPure_1655_, lean_box(0), v_a_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__2(lean_object* v_toFunctor_1659_, lean_object* v_f_1660_, lean_object* v_intoError_1661_, lean_object* v_s_1662_, lean_object* v_a_1663_, lean_object* v_b_1664_){
_start:
{
lean_object* v_map_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1674_; 
v_map_1665_ = lean_ctor_get(v_toFunctor_1659_, 0);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_toFunctor_1659_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; 
v_unused_1675_ = lean_ctor_get(v_toFunctor_1659_, 1);
lean_dec(v_unused_1675_);
v___x_1667_ = v_toFunctor_1659_;
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_map_1665_);
lean_dec(v_toFunctor_1659_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1674_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
lean_ctor_set(v___x_1667_, 1, v_b_1664_);
lean_ctor_set(v___x_1667_, 0, v_a_1663_);
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_a_1663_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_b_1664_);
v___x_1670_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = lean_apply_2(v_f_1660_, v___x_1670_, v_s_1662_);
v___x_1672_ = lean_apply_4(v_map_1665_, lean_box(0), lean_box(0), v_intoError_1661_, v___x_1671_);
return v___x_1672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg(lean_object* v_inst_1677_, lean_object* v_map_1678_, lean_object* v_init_1679_, lean_object* v_f_1680_){
_start:
{
lean_object* v_toApplicative_1681_; lean_object* v_toBind_1682_; lean_object* v___f_1683_; lean_object* v___f_1684_; lean_object* v___f_1685_; lean_object* v___f_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_toFunctor_1693_; lean_object* v_toPure_1694_; lean_object* v_intoError_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_toApplicative_1681_ = lean_ctor_get(v_inst_1677_, 0);
lean_inc_ref(v_toApplicative_1681_);
v_toBind_1682_ = lean_ctor_get(v_inst_1677_, 1);
lean_inc(v_toBind_1682_);
lean_inc_ref_n(v_inst_1677_, 6);
v___f_1683_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1683_, 0, v_inst_1677_);
v___f_1684_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1684_, 0, v_inst_1677_);
v___f_1685_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1685_, 0, v_inst_1677_);
v___f_1686_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1686_, 0, v_inst_1677_);
v___x_1687_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1687_, 0, lean_box(0));
lean_closure_set(v___x_1687_, 1, lean_box(0));
lean_closure_set(v___x_1687_, 2, v_inst_1677_);
v___x_1688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v___f_1683_);
v___x_1689_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1689_, 0, lean_box(0));
lean_closure_set(v___x_1689_, 1, lean_box(0));
lean_closure_set(v___x_1689_, 2, v_inst_1677_);
v___x_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
lean_ctor_set(v___x_1690_, 2, v___f_1684_);
lean_ctor_set(v___x_1690_, 3, v___f_1685_);
lean_ctor_set(v___x_1690_, 4, v___f_1686_);
v___x_1691_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1691_, 0, lean_box(0));
lean_closure_set(v___x_1691_, 1, lean_box(0));
lean_closure_set(v___x_1691_, 2, v_inst_1677_);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1690_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v_toFunctor_1693_ = lean_ctor_get(v_toApplicative_1681_, 0);
lean_inc_ref(v_toFunctor_1693_);
v_toPure_1694_ = lean_ctor_get(v_toApplicative_1681_, 1);
lean_inc(v_toPure_1694_);
lean_dec_ref(v_toApplicative_1681_);
v_intoError_1695_ = ((lean_object*)(l_Lean_PersistentHashMap_forIn___redArg___closed__0));
v___f_1696_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1696_, 0, v_toPure_1694_);
v___f_1697_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__2), 6, 3);
lean_closure_set(v___f_1697_, 0, v_toFunctor_1693_);
lean_closure_set(v___f_1697_, 1, v_f_1680_);
lean_closure_set(v___f_1697_, 2, v_intoError_1695_);
lean_inc_ref(v_map_1678_);
v___x_1698_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1692_, v___f_1697_, v_map_1678_, v_init_1679_);
v___x_1699_ = lean_apply_4(v_toBind_1682_, lean_box(0), lean_box(0), v___x_1698_, v___f_1696_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___boxed(lean_object* v_inst_1700_, lean_object* v_map_1701_, lean_object* v_init_1702_, lean_object* v_f_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1700_, v_map_1701_, v_init_1702_, v_f_1703_);
lean_dec_ref(v_map_1701_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn(lean_object* v_m_1705_, lean_object* v_00_u03c3_1706_, lean_object* v_00_u03b1_1707_, lean_object* v_00_u03b2_1708_, lean_object* v_x_1709_, lean_object* v_x_1710_, lean_object* v_inst_1711_, lean_object* v_map_1712_, lean_object* v_init_1713_, lean_object* v_f_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1711_, v_map_1712_, v_init_1713_, v_f_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___boxed(lean_object* v_m_1716_, lean_object* v_00_u03c3_1717_, lean_object* v_00_u03b1_1718_, lean_object* v_00_u03b2_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_, lean_object* v_inst_1722_, lean_object* v_map_1723_, lean_object* v_init_1724_, lean_object* v_f_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_PersistentHashMap_forIn(v_m_1716_, v_00_u03c3_1717_, v_00_u03b1_1718_, v_00_u03b2_1719_, v_x_1720_, v_x_1721_, v_inst_1722_, v_map_1723_, v_init_1724_, v_f_1725_);
lean_dec_ref(v_map_1723_);
lean_dec_ref(v_x_1721_);
lean_dec_ref(v_x_1720_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_inst_1727_, lean_object* v_00_u03b2_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1727_, v___y_1729_, v___y_1730_, v___y_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed(lean_object* v_inst_1733_, lean_object* v_00_u03b2_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(v_inst_1733_, v_00_u03b2_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec_ref(v___y_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1739_){
_start:
{
lean_object* v___f_1740_; 
v___f_1740_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1740_, 0, v_inst_1739_);
return v___f_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad(lean_object* v_m_1741_, lean_object* v_00_u03b1_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_, lean_object* v_inst_1746_){
_start:
{
lean_object* v___f_1747_; 
v___f_1747_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1747_, 0, v_inst_1746_);
return v___f_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___boxed(lean_object* v_m_1748_, lean_object* v_00_u03b1_1749_, lean_object* v_00_u03b2_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_, lean_object* v_inst_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_PersistentHashMap_instForInProdOfMonad(v_m_1748_, v_00_u03b1_1749_, v_00_u03b2_1750_, v_x_1751_, v_x_1752_, v_inst_1753_);
lean_dec_ref(v_x_1752_);
lean_dec_ref(v_x_1751_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__0(lean_object* v_toPure_1755_, lean_object* v_entries_x27_1756_){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_entries_x27_1756_);
v___x_1758_ = lean_apply_2(v_toPure_1755_, lean_box(0), v___x_1757_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__1(lean_object* v_toPure_1759_, lean_object* v_____do__lift_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_____do__lift_1760_);
v___x_1762_ = lean_apply_2(v_toPure_1759_, lean_box(0), v___x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__2(lean_object* v_key_1763_, lean_object* v_toPure_1764_, lean_object* v_____do__lift_1765_){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_key_1763_);
lean_ctor_set(v___x_1766_, 1, v_____do__lift_1765_);
v___x_1767_ = lean_apply_2(v_toPure_1764_, lean_box(0), v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__4(lean_object* v_ks_1768_, lean_object* v_toPure_1769_, lean_object* v_____x_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1771_, 0, v_ks_1768_);
lean_ctor_set(v___x_1771_, 1, v_____x_1770_);
v___x_1772_ = lean_apply_2(v_toPure_1769_, lean_box(0), v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg(lean_object* v_inst_1773_, lean_object* v_f_1774_, lean_object* v_n_1775_){
_start:
{
if (lean_obj_tag(v_n_1775_) == 0)
{
lean_object* v_toApplicative_1776_; lean_object* v_toBind_1777_; lean_object* v_toPure_1778_; lean_object* v_es_1779_; lean_object* v___f_1780_; lean_object* v___f_1781_; lean_object* v___f_1782_; size_t v_sz_1783_; size_t v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v_toApplicative_1776_ = lean_ctor_get(v_inst_1773_, 0);
v_toBind_1777_ = lean_ctor_get(v_inst_1773_, 1);
lean_inc_n(v_toBind_1777_, 2);
v_toPure_1778_ = lean_ctor_get(v_toApplicative_1776_, 1);
v_es_1779_ = lean_ctor_get(v_n_1775_, 0);
lean_inc_ref(v_es_1779_);
lean_dec_ref_known(v_n_1775_, 1);
lean_inc_n(v_toPure_1778_, 3);
v___f_1780_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1780_, 0, v_toPure_1778_);
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1781_, 0, v_toPure_1778_);
lean_inc_ref(v_inst_1773_);
v___f_1782_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1782_, 0, v_toPure_1778_);
lean_closure_set(v___f_1782_, 1, v_f_1774_);
lean_closure_set(v___f_1782_, 2, v_toBind_1777_);
lean_closure_set(v___f_1782_, 3, v_inst_1773_);
lean_closure_set(v___f_1782_, 4, v___f_1781_);
v_sz_1783_ = lean_array_size(v_es_1779_);
v___x_1784_ = ((size_t)0ULL);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1773_, v___f_1782_, v_sz_1783_, v___x_1784_, v_es_1779_);
v___x_1786_ = lean_apply_4(v_toBind_1777_, lean_box(0), lean_box(0), v___x_1785_, v___f_1780_);
return v___x_1786_;
}
else
{
lean_object* v_toApplicative_1787_; lean_object* v_toBind_1788_; lean_object* v_toPure_1789_; lean_object* v_ks_1790_; lean_object* v_vs_1791_; lean_object* v___f_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_toApplicative_1787_ = lean_ctor_get(v_inst_1773_, 0);
v_toBind_1788_ = lean_ctor_get(v_inst_1773_, 1);
lean_inc(v_toBind_1788_);
v_toPure_1789_ = lean_ctor_get(v_toApplicative_1787_, 1);
v_ks_1790_ = lean_ctor_get(v_n_1775_, 0);
lean_inc_ref(v_ks_1790_);
v_vs_1791_ = lean_ctor_get(v_n_1775_, 1);
lean_inc_ref(v_vs_1791_);
lean_dec_ref_known(v_n_1775_, 2);
lean_inc(v_toPure_1789_);
v___f_1792_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__4), 3, 2);
lean_closure_set(v___f_1792_, 0, v_ks_1790_);
lean_closure_set(v___f_1792_, 1, v_toPure_1789_);
v___x_1793_ = l_Array_mapM_x27___redArg(v_inst_1773_, v_f_1774_, v_vs_1791_);
v___x_1794_ = lean_apply_4(v_toBind_1788_, lean_box(0), lean_box(0), v___x_1793_, v___f_1792_);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__3(lean_object* v_toPure_1795_, lean_object* v_f_1796_, lean_object* v_toBind_1797_, lean_object* v_inst_1798_, lean_object* v___f_1799_, lean_object* v_x_1800_){
_start:
{
switch(lean_obj_tag(v_x_1800_))
{
case 0:
{
lean_object* v_key_1801_; lean_object* v_val_1802_; lean_object* v___f_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v___f_1799_);
lean_dec_ref(v_inst_1798_);
v_key_1801_ = lean_ctor_get(v_x_1800_, 0);
lean_inc(v_key_1801_);
v_val_1802_ = lean_ctor_get(v_x_1800_, 1);
lean_inc(v_val_1802_);
lean_dec_ref_known(v_x_1800_, 2);
v___f_1803_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1803_, 0, v_key_1801_);
lean_closure_set(v___f_1803_, 1, v_toPure_1795_);
v___x_1804_ = lean_apply_1(v_f_1796_, v_val_1802_);
v___x_1805_ = lean_apply_4(v_toBind_1797_, lean_box(0), lean_box(0), v___x_1804_, v___f_1803_);
return v___x_1805_;
}
case 1:
{
lean_object* v_node_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
lean_dec(v_toPure_1795_);
v_node_1806_ = lean_ctor_get(v_x_1800_, 0);
lean_inc(v_node_1806_);
lean_dec_ref_known(v_x_1800_, 1);
v___x_1807_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1798_, v_f_1796_, v_node_1806_);
v___x_1808_ = lean_apply_4(v_toBind_1797_, lean_box(0), lean_box(0), v___x_1807_, v___f_1799_);
return v___x_1808_;
}
default: 
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v___f_1799_);
lean_dec_ref(v_inst_1798_);
lean_dec(v_toBind_1797_);
lean_dec(v_f_1796_);
v___x_1809_ = lean_box(2);
v___x_1810_ = lean_apply_2(v_toPure_1795_, lean_box(0), v___x_1809_);
return v___x_1810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux(lean_object* v_00_u03b1_1811_, lean_object* v_00_u03b2_1812_, lean_object* v_00_u03c3_1813_, lean_object* v_m_1814_, lean_object* v_inst_1815_, lean_object* v_f_1816_, lean_object* v_n_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1815_, v_f_1816_, v_n_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg___lam__0(lean_object* v_toPure_1819_, lean_object* v_root_1820_){
_start:
{
lean_object* v___x_1821_; 
v___x_1821_ = lean_apply_2(v_toPure_1819_, lean_box(0), v_root_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object* v_inst_1822_, lean_object* v_pm_1823_, lean_object* v_f_1824_){
_start:
{
lean_object* v_toApplicative_1825_; lean_object* v_toBind_1826_; lean_object* v_toPure_1827_; lean_object* v___x_1828_; lean_object* v___f_1829_; lean_object* v___x_1830_; 
v_toApplicative_1825_ = lean_ctor_get(v_inst_1822_, 0);
v_toBind_1826_ = lean_ctor_get(v_inst_1822_, 1);
lean_inc(v_toBind_1826_);
v_toPure_1827_ = lean_ctor_get(v_toApplicative_1825_, 1);
lean_inc(v_toPure_1827_);
v___x_1828_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1822_, v_f_1824_, v_pm_1823_);
v___f_1829_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1829_, 0, v_toPure_1827_);
v___x_1830_ = lean_apply_4(v_toBind_1826_, lean_box(0), lean_box(0), v___x_1828_, v___f_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM(lean_object* v_00_u03b1_1831_, lean_object* v_00_u03b2_1832_, lean_object* v_00_u03c3_1833_, lean_object* v_m_1834_, lean_object* v_inst_1835_, lean_object* v_x_1836_, lean_object* v_x_1837_, lean_object* v_pm_1838_, lean_object* v_f_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_1835_, v_pm_1838_, v_f_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___boxed(lean_object* v_00_u03b1_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_00_u03c3_1843_, lean_object* v_m_1844_, lean_object* v_inst_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_pm_1848_, lean_object* v_f_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_PersistentHashMap_mapM(v_00_u03b1_1841_, v_00_u03b2_1842_, v_00_u03c3_1843_, v_m_1844_, v_inst_1845_, v_x_1846_, v_x_1847_, v_pm_1848_, v_f_1849_);
lean_dec_ref(v_x_1847_);
lean_dec_ref(v_x_1846_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg___lam__0(lean_object* v_f_1851_, lean_object* v_x_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_apply_1(v_f_1851_, v_x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg(lean_object* v_pm_1854_, lean_object* v_f_1855_){
_start:
{
lean_object* v___f_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___f_1856_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1856_, 0, v_f_1855_);
v___x_1857_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1858_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_1857_, v_pm_1854_, v___f_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map(lean_object* v_00_u03b1_1859_, lean_object* v_00_u03b2_1860_, lean_object* v_00_u03c3_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_, lean_object* v_pm_1864_, lean_object* v_f_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_PersistentHashMap_map___redArg(v_pm_1864_, v_f_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___boxed(lean_object* v_00_u03b1_1867_, lean_object* v_00_u03b2_1868_, lean_object* v_00_u03c3_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_, lean_object* v_pm_1872_, lean_object* v_f_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_PersistentHashMap_map(v_00_u03b1_1867_, v_00_u03b2_1868_, v_00_u03c3_1869_, v_x_1870_, v_x_1871_, v_pm_1872_, v_f_1873_);
lean_dec_ref(v_x_1871_);
lean_dec_ref(v_x_1870_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg___lam__0(lean_object* v_ps_1875_, lean_object* v_k_1876_, lean_object* v_v_1877_){
_start:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1878_, 0, v_k_1876_);
lean_ctor_set(v___x_1878_, 1, v_v_1877_);
v___x_1879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v_ps_1875_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg(lean_object* v_m_1881_){
_start:
{
lean_object* v___f_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___f_1882_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___redArg___closed__0));
v___x_1883_ = lean_box(0);
v___x_1884_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1881_, v___f_1882_, v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList(lean_object* v_00_u03b1_1885_, lean_object* v_00_u03b2_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_, lean_object* v_m_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_PersistentHashMap_toList___redArg(v_m_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___boxed(lean_object* v_00_u03b1_1891_, lean_object* v_00_u03b2_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_m_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_PersistentHashMap_toList(v_00_u03b1_1891_, v_00_u03b2_1892_, v_x_1893_, v_x_1894_, v_m_1895_);
lean_dec_ref(v_x_1894_);
lean_dec_ref(v_x_1893_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg___lam__0(lean_object* v_ps_1897_, lean_object* v_k_1898_, lean_object* v_v_1899_){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1900_, 0, v_k_1898_);
lean_ctor_set(v___x_1900_, 1, v_v_1899_);
v___x_1901_ = lean_array_push(v_ps_1897_, v___x_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg(lean_object* v_m_1905_){
_start:
{
lean_object* v___f_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___f_1906_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__0));
v___x_1907_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__1));
v___x_1908_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1905_, v___f_1906_, v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray(lean_object* v_00_u03b1_1909_, lean_object* v_00_u03b2_1910_, lean_object* v_x_1911_, lean_object* v_x_1912_, lean_object* v_m_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_PersistentHashMap_toArray___redArg(v_m_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___boxed(lean_object* v_00_u03b1_1915_, lean_object* v_00_u03b2_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_, lean_object* v_m_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_PersistentHashMap_toArray(v_00_u03b1_1915_, v_00_u03b2_1916_, v_x_1917_, v_x_1918_, v_m_1919_);
lean_dec_ref(v_x_1918_);
lean_dec_ref(v_x_1917_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg(lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
if (lean_obj_tag(v_x_1921_) == 0)
{
lean_object* v_es_1924_; lean_object* v_numNodes_1925_; lean_object* v_numNull_1926_; lean_object* v_numCollisions_1927_; lean_object* v_maxDepth_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1950_; 
v_es_1924_ = lean_ctor_get(v_x_1921_, 0);
v_numNodes_1925_ = lean_ctor_get(v_x_1922_, 0);
v_numNull_1926_ = lean_ctor_get(v_x_1922_, 1);
v_numCollisions_1927_ = lean_ctor_get(v_x_1922_, 2);
v_maxDepth_1928_ = lean_ctor_get(v_x_1922_, 3);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_x_1922_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1930_ = v_x_1922_;
v_isShared_1931_ = v_isSharedCheck_1950_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_maxDepth_1928_);
lean_inc(v_numCollisions_1927_);
lean_inc(v_numNull_1926_);
lean_inc(v_numNodes_1925_);
lean_dec(v_x_1922_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1950_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___y_1935_; uint8_t v___x_1949_; 
v___x_1932_ = lean_unsigned_to_nat(1u);
v___x_1933_ = lean_nat_add(v_numNodes_1925_, v___x_1932_);
lean_dec(v_numNodes_1925_);
v___x_1949_ = lean_nat_dec_le(v_maxDepth_1928_, v_x_1923_);
if (v___x_1949_ == 0)
{
v___y_1935_ = v_maxDepth_1928_;
goto v___jp_1934_;
}
else
{
lean_dec(v_maxDepth_1928_);
lean_inc(v_x_1923_);
v___y_1935_ = v_x_1923_;
goto v___jp_1934_;
}
v___jp_1934_:
{
lean_object* v_stats_1937_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 3, v___y_1935_);
lean_ctor_set(v___x_1930_, 0, v___x_1933_);
v_stats_1937_ = v___x_1930_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_numNull_1926_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_numCollisions_1927_);
lean_ctor_set(v_reuseFailAlloc_1948_, 3, v___y_1935_);
v_stats_1937_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; uint8_t v___x_1940_; 
v___x_1938_ = lean_unsigned_to_nat(0u);
v___x_1939_ = lean_array_get_size(v_es_1924_);
v___x_1940_ = lean_nat_dec_lt(v___x_1938_, v___x_1939_);
if (v___x_1940_ == 0)
{
lean_dec(v_x_1923_);
return v_stats_1937_;
}
else
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_nat_dec_le(v___x_1939_, v___x_1939_);
if (v___x_1941_ == 0)
{
if (v___x_1940_ == 0)
{
lean_dec(v_x_1923_);
return v_stats_1937_;
}
else
{
size_t v___x_1942_; size_t v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = ((size_t)0ULL);
v___x_1943_ = lean_usize_of_nat(v___x_1939_);
v___x_1944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1923_, v_es_1924_, v___x_1942_, v___x_1943_, v_stats_1937_);
lean_dec(v_x_1923_);
return v___x_1944_;
}
}
else
{
size_t v___x_1945_; size_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = ((size_t)0ULL);
v___x_1946_ = lean_usize_of_nat(v___x_1939_);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1923_, v_es_1924_, v___x_1945_, v___x_1946_, v_stats_1937_);
lean_dec(v_x_1923_);
return v___x_1947_;
}
}
}
}
}
}
else
{
lean_object* v_ks_1951_; lean_object* v_numNodes_1952_; lean_object* v_numNull_1953_; lean_object* v_numCollisions_1954_; lean_object* v_maxDepth_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1971_; 
v_ks_1951_ = lean_ctor_get(v_x_1921_, 0);
v_numNodes_1952_ = lean_ctor_get(v_x_1922_, 0);
v_numNull_1953_ = lean_ctor_get(v_x_1922_, 1);
v_numCollisions_1954_ = lean_ctor_get(v_x_1922_, 2);
v_maxDepth_1955_ = lean_ctor_get(v_x_1922_, 3);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_x_1922_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1957_ = v_x_1922_;
v_isShared_1958_ = v_isSharedCheck_1971_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_maxDepth_1955_);
lean_inc(v_numCollisions_1954_);
lean_inc(v_numNull_1953_);
lean_inc(v_numNodes_1952_);
lean_dec(v_x_1922_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1971_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1959_ = lean_unsigned_to_nat(1u);
v___x_1960_ = lean_nat_add(v_numNodes_1952_, v___x_1959_);
lean_dec(v_numNodes_1952_);
v___x_1961_ = lean_array_get_size(v_ks_1951_);
v___x_1962_ = lean_nat_add(v_numCollisions_1954_, v___x_1961_);
lean_dec(v_numCollisions_1954_);
v___x_1963_ = lean_nat_sub(v___x_1962_, v___x_1959_);
lean_dec(v___x_1962_);
v___x_1964_ = lean_nat_dec_le(v_maxDepth_1955_, v_x_1923_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1966_; 
lean_dec(v_x_1923_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 2, v___x_1963_);
lean_ctor_set(v___x_1957_, 0, v___x_1960_);
v___x_1966_ = v___x_1957_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_numNull_1953_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_maxDepth_1955_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
else
{
lean_object* v___x_1969_; 
lean_dec(v_maxDepth_1955_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 3, v_x_1923_);
lean_ctor_set(v___x_1957_, 2, v___x_1963_);
lean_ctor_set(v___x_1957_, 0, v___x_1960_);
v___x_1969_ = v___x_1957_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1970_, 1, v_numNull_1953_);
lean_ctor_set(v_reuseFailAlloc_1970_, 2, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1970_, 3, v_x_1923_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(lean_object* v_x_1972_, lean_object* v_as_1973_, size_t v_i_1974_, size_t v_stop_1975_, lean_object* v_b_1976_){
_start:
{
lean_object* v___y_1978_; uint8_t v___x_1982_; 
v___x_1982_ = lean_usize_dec_eq(v_i_1974_, v_stop_1975_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = lean_unsigned_to_nat(1u);
v___x_1984_ = lean_array_uget_borrowed(v_as_1973_, v_i_1974_);
switch(lean_obj_tag(v___x_1984_))
{
case 0:
{
v___y_1978_ = v_b_1976_;
goto v___jp_1977_;
}
case 1:
{
lean_object* v_node_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_node_1985_ = lean_ctor_get(v___x_1984_, 0);
v___x_1986_ = lean_nat_add(v_x_1972_, v___x_1983_);
v___x_1987_ = l_Lean_PersistentHashMap_collectStats___redArg(v_node_1985_, v_b_1976_, v___x_1986_);
v___y_1978_ = v___x_1987_;
goto v___jp_1977_;
}
default: 
{
lean_object* v_numNodes_1988_; lean_object* v_numNull_1989_; lean_object* v_numCollisions_1990_; lean_object* v_maxDepth_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1999_; 
v_numNodes_1988_ = lean_ctor_get(v_b_1976_, 0);
v_numNull_1989_ = lean_ctor_get(v_b_1976_, 1);
v_numCollisions_1990_ = lean_ctor_get(v_b_1976_, 2);
v_maxDepth_1991_ = lean_ctor_get(v_b_1976_, 3);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_b_1976_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1993_ = v_b_1976_;
v_isShared_1994_ = v_isSharedCheck_1999_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_maxDepth_1991_);
lean_inc(v_numCollisions_1990_);
lean_inc(v_numNull_1989_);
lean_inc(v_numNodes_1988_);
lean_dec(v_b_1976_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1999_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1995_; lean_object* v___x_1997_; 
v___x_1995_ = lean_nat_add(v_numNull_1989_, v___x_1983_);
lean_dec(v_numNull_1989_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 1, v___x_1995_);
v___x_1997_ = v___x_1993_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_numNodes_1988_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v_numCollisions_1990_);
lean_ctor_set(v_reuseFailAlloc_1998_, 3, v_maxDepth_1991_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
v___y_1978_ = v___x_1997_;
goto v___jp_1977_;
}
}
}
}
}
else
{
return v_b_1976_;
}
v___jp_1977_:
{
size_t v___x_1979_; size_t v___x_1980_; 
v___x_1979_ = ((size_t)1ULL);
v___x_1980_ = lean_usize_add(v_i_1974_, v___x_1979_);
v_i_1974_ = v___x_1980_;
v_b_1976_ = v___y_1978_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg___boxed(lean_object* v_x_2000_, lean_object* v_as_2001_, lean_object* v_i_2002_, lean_object* v_stop_2003_, lean_object* v_b_2004_){
_start:
{
size_t v_i_boxed_2005_; size_t v_stop_boxed_2006_; lean_object* v_res_2007_; 
v_i_boxed_2005_ = lean_unbox_usize(v_i_2002_);
lean_dec(v_i_2002_);
v_stop_boxed_2006_ = lean_unbox_usize(v_stop_2003_);
lean_dec(v_stop_2003_);
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2000_, v_as_2001_, v_i_boxed_2005_, v_stop_boxed_2006_, v_b_2004_);
lean_dec_ref(v_as_2001_);
lean_dec(v_x_2000_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg___boxed(lean_object* v_x_2008_, lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2008_, v_x_2009_, v_x_2010_);
lean_dec_ref(v_x_2008_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats(lean_object* v_00_u03b1_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_x_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2014_, v_x_2015_, v_x_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___boxed(lean_object* v_00_u03b1_2018_, lean_object* v_00_u03b2_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Lean_PersistentHashMap_collectStats(v_00_u03b1_2018_, v_00_u03b2_2019_, v_x_2020_, v_x_2021_, v_x_2022_);
lean_dec_ref(v_x_2020_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_x_2026_, lean_object* v_as_2027_, size_t v_i_2028_, size_t v_stop_2029_, lean_object* v_b_2030_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2026_, v_as_2027_, v_i_2028_, v_stop_2029_, v_b_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2032_, lean_object* v_00_u03b2_2033_, lean_object* v_x_2034_, lean_object* v_as_2035_, lean_object* v_i_2036_, lean_object* v_stop_2037_, lean_object* v_b_2038_){
_start:
{
size_t v_i_boxed_2039_; size_t v_stop_boxed_2040_; lean_object* v_res_2041_; 
v_i_boxed_2039_ = lean_unbox_usize(v_i_2036_);
lean_dec(v_i_2036_);
v_stop_boxed_2040_ = lean_unbox_usize(v_stop_2037_);
lean_dec(v_stop_2037_);
v_res_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(v_00_u03b1_2032_, v_00_u03b2_2033_, v_x_2034_, v_as_2035_, v_i_boxed_2039_, v_stop_boxed_2040_, v_b_2038_);
lean_dec_ref(v_as_2035_);
lean_dec(v_x_2034_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg(lean_object* v_m_2044_){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = ((lean_object*)(l_Lean_PersistentHashMap_stats___redArg___closed__0));
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = l_Lean_PersistentHashMap_collectStats___redArg(v_m_2044_, v___x_2045_, v___x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg___boxed(lean_object* v_m_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2048_);
lean_dec_ref(v_m_2048_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats(lean_object* v_00_u03b1_2050_, lean_object* v_00_u03b2_2051_, lean_object* v_x_2052_, lean_object* v_x_2053_, lean_object* v_m_2054_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2054_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___boxed(lean_object* v_00_u03b1_2056_, lean_object* v_00_u03b2_2057_, lean_object* v_x_2058_, lean_object* v_x_2059_, lean_object* v_m_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Lean_PersistentHashMap_stats(v_00_u03b1_2056_, v_00_u03b2_2057_, v_x_2058_, v_x_2059_, v_m_2060_);
lean_dec_ref(v_m_2060_);
lean_dec_ref(v_x_2059_);
lean_dec_ref(v_x_2058_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Stats_toString(lean_object* v_s_2067_){
_start:
{
lean_object* v_numNodes_2068_; lean_object* v_numNull_2069_; lean_object* v_numCollisions_2070_; lean_object* v_maxDepth_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_numNodes_2068_ = lean_ctor_get(v_s_2067_, 0);
lean_inc(v_numNodes_2068_);
v_numNull_2069_ = lean_ctor_get(v_s_2067_, 1);
lean_inc(v_numNull_2069_);
v_numCollisions_2070_ = lean_ctor_get(v_s_2067_, 2);
lean_inc(v_numCollisions_2070_);
v_maxDepth_2071_ = lean_ctor_get(v_s_2067_, 3);
lean_inc(v_maxDepth_2071_);
lean_dec_ref(v_s_2067_);
v___x_2072_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__0));
v___x_2073_ = l_Nat_reprFast(v_numNodes_2068_);
v___x_2074_ = lean_string_append(v___x_2072_, v___x_2073_);
lean_dec_ref(v___x_2073_);
v___x_2075_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__1));
v___x_2076_ = lean_string_append(v___x_2074_, v___x_2075_);
v___x_2077_ = l_Nat_reprFast(v_numNull_2069_);
v___x_2078_ = lean_string_append(v___x_2076_, v___x_2077_);
lean_dec_ref(v___x_2077_);
v___x_2079_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__2));
v___x_2080_ = lean_string_append(v___x_2078_, v___x_2079_);
v___x_2081_ = l_Nat_reprFast(v_numCollisions_2070_);
v___x_2082_ = lean_string_append(v___x_2080_, v___x_2081_);
lean_dec_ref(v___x_2081_);
v___x_2083_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__3));
v___x_2084_ = lean_string_append(v___x_2082_, v___x_2083_);
v___x_2085_ = l_Nat_reprFast(v_maxDepth_2071_);
v___x_2086_ = lean_string_append(v___x_2084_, v___x_2085_);
lean_dec_ref(v___x_2085_);
v___x_2087_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__4));
v___x_2088_ = lean_string_append(v___x_2086_, v___x_2087_);
return v___x_2088_;
}
}
lean_object* runtime_initialize_Init_Data_Array_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_PersistentHashMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Array_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentHashMap_shift = _init_l_Lean_PersistentHashMap_shift();
l_Lean_PersistentHashMap_branching = _init_l_Lean_PersistentHashMap_branching();
l_Lean_PersistentHashMap_maxDepth = _init_l_Lean_PersistentHashMap_maxDepth();
l_Lean_PersistentHashMap_maxCollisions = _init_l_Lean_PersistentHashMap_maxCollisions();
lean_mark_persistent(l_Lean_PersistentHashMap_maxCollisions);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_PersistentHashMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Array_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_Except(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_PersistentHashMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Except(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_PersistentHashMap(builtin);
}
#ifdef __cplusplus
}
#endif
