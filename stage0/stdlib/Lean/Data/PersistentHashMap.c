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
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(lean_object* v_as_135_, size_t v_i_136_, size_t v_stop_137_){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = lean_usize_dec_eq(v_i_136_, v_stop_137_);
if (v___x_138_ == 0)
{
uint8_t v___x_139_; uint8_t v___y_141_; lean_object* v___x_145_; 
v___x_139_ = 1;
v___x_145_ = lean_array_uget_borrowed(v_as_135_, v_i_136_);
switch(lean_obj_tag(v___x_145_))
{
case 0:
{
return v___x_139_;
}
case 1:
{
lean_object* v_node_146_; uint8_t v___x_147_; 
v_node_146_ = lean_ctor_get(v___x_145_, 0);
v___x_147_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_node_146_);
if (v___x_147_ == 0)
{
return v___x_139_;
}
else
{
v___y_141_ = v___x_138_;
goto v___jp_140_;
}
}
default: 
{
v___y_141_ = v___x_138_;
goto v___jp_140_;
}
}
v___jp_140_:
{
if (v___y_141_ == 0)
{
size_t v___x_142_; size_t v___x_143_; 
v___x_142_ = ((size_t)1ULL);
v___x_143_ = lean_usize_add(v_i_136_, v___x_142_);
v_i_136_ = v___x_143_;
goto _start;
}
else
{
return v___x_139_;
}
}
}
else
{
uint8_t v___x_148_; 
v___x_148_ = 0;
return v___x_148_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_149_) == 0)
{
lean_object* v_es_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v_es_150_ = lean_ctor_get(v_x_149_, 0);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_array_get_size(v_es_150_);
v___x_153_ = lean_nat_dec_lt(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
uint8_t v___x_154_; 
v___x_154_ = 1;
return v___x_154_;
}
else
{
if (v___x_153_ == 0)
{
return v___x_153_;
}
else
{
size_t v___x_155_; size_t v___x_156_; uint8_t v___x_157_; 
v___x_155_ = ((size_t)0ULL);
v___x_156_ = lean_usize_of_nat(v___x_152_);
v___x_157_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_es_150_, v___x_155_, v___x_156_);
if (v___x_157_ == 0)
{
return v___x_153_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
}
}
}
else
{
uint8_t v___x_159_; 
v___x_159_ = 0;
return v___x_159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_isEmpty___redArg___boxed(lean_object* v_x_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_160_);
lean_dec_ref(v_x_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg___boxed(lean_object* v_as_163_, lean_object* v_i_164_, lean_object* v_stop_165_){
_start:
{
size_t v_i_boxed_166_; size_t v_stop_boxed_167_; uint8_t v_res_168_; lean_object* v_r_169_; 
v_i_boxed_166_ = lean_unbox_usize(v_i_164_);
lean_dec(v_i_164_);
v_stop_boxed_167_ = lean_unbox_usize(v_stop_165_);
lean_dec(v_stop_165_);
v_res_168_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_as_163_, v_i_boxed_166_, v_stop_boxed_167_);
lean_dec_ref(v_as_163_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_Node_isEmpty(lean_object* v_00_u03b1_170_, lean_object* v_00_u03b2_171_, lean_object* v_x_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_isEmpty___boxed(lean_object* v_00_u03b1_174_, lean_object* v_00_u03b2_175_, lean_object* v_x_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Lean_PersistentHashMap_Node_isEmpty(v_00_u03b1_174_, v_00_u03b2_175_, v_x_176_);
lean_dec_ref(v_x_176_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_as_181_, size_t v_i_182_, size_t v_stop_183_){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_as_181_, v_i_182_, v_stop_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___boxed(lean_object* v_00_u03b1_185_, lean_object* v_00_u03b2_186_, lean_object* v_as_187_, lean_object* v_i_188_, lean_object* v_stop_189_){
_start:
{
size_t v_i_boxed_190_; size_t v_stop_boxed_191_; uint8_t v_res_192_; lean_object* v_r_193_; 
v_i_boxed_190_ = lean_unbox_usize(v_i_188_);
lean_dec(v_i_188_);
v_stop_boxed_191_ = lean_unbox_usize(v_stop_189_);
lean_dec(v_stop_189_);
v_res_192_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(v_00_u03b1_185_, v_00_u03b2_186_, v_as_187_, v_i_boxed_190_, v_stop_boxed_191_);
lean_dec_ref(v_as_187_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode(lean_object* v_00_u03b1_198_, lean_object* v_00_u03b2_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = ((lean_object*)(l_Lean_PersistentHashMap_instInhabitedNode___closed__1));
return v___x_200_;
}
}
static size_t _init_l_Lean_PersistentHashMap_shift(void){
_start:
{
size_t v___x_201_; 
v___x_201_ = ((size_t)5ULL);
return v___x_201_;
}
}
static size_t _init_l_Lean_PersistentHashMap_branching(void){
_start:
{
size_t v___x_202_; 
v___x_202_ = ((size_t)32ULL);
return v___x_202_;
}
}
static size_t _init_l_Lean_PersistentHashMap_maxDepth(void){
_start:
{
size_t v___x_203_; 
v___x_203_ = ((size_t)7ULL);
return v___x_203_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_maxCollisions(void){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_unsigned_to_nat(4u);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_box(2);
v___x_206_ = lean_unsigned_to_nat(32u);
v___x_207_ = lean_mk_array(v___x_206_, v___x_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___closed__0(void){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_211_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___closed__1(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___closed__0, &l_Lean_PersistentHashMap_empty___closed__0_once, _init_l_Lean_PersistentHashMap_empty___closed__0);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_inst_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___closed__1, &l_Lean_PersistentHashMap_empty___closed__1_once, _init_l_Lean_PersistentHashMap_empty___closed__1);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___boxed(lean_object* v_00_u03b1_219_, lean_object* v_00_u03b2_220_, lean_object* v_inst_221_, lean_object* v_inst_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_PersistentHashMap_empty(v_00_u03b1_219_, v_00_u03b2_220_, v_inst_221_, v_inst_222_);
lean_dec_ref(v_inst_222_);
lean_dec_ref(v_inst_221_);
return v_res_223_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___redArg(lean_object* v_x_224_){
_start:
{
uint8_t v___x_225_; 
v___x_225_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___redArg___boxed(lean_object* v_x_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_Lean_PersistentHashMap_isEmpty___redArg(v_x_226_);
lean_dec_ref(v_x_226_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty(lean_object* v_00_u03b1_229_, lean_object* v_00_u03b2_230_, lean_object* v_x_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___boxed(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
uint8_t v_res_240_; lean_object* v_r_241_; 
v_res_240_ = l_Lean_PersistentHashMap_isEmpty(v_00_u03b1_235_, v_00_u03b2_236_, v_x_237_, v_x_238_, v_x_239_);
lean_dec_ref(v_x_239_);
lean_dec_ref(v_x_238_);
lean_dec_ref(v_x_237_);
v_r_241_ = lean_box(v_res_240_);
return v_r_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_inst_244_, lean_object* v_inst_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___closed__1, &l_Lean_PersistentHashMap_empty___closed__1_once, _init_l_Lean_PersistentHashMap_empty___closed__1);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___boxed(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_inst_249_, lean_object* v_inst_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_PersistentHashMap_instInhabited(v_00_u03b1_247_, v_00_u03b2_248_, v_inst_249_, v_inst_250_);
lean_dec_ref(v_inst_250_);
lean_dec_ref(v_inst_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___closed__1, &l_Lean_PersistentHashMap_empty___closed__1_once, _init_l_Lean_PersistentHashMap_empty___closed__1);
return v___x_254_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_mul2Shift(size_t v_i_255_, size_t v_shift_256_){
_start:
{
size_t v___x_257_; 
v___x_257_ = lean_usize_shift_left(v_i_255_, v_shift_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mul2Shift___boxed(lean_object* v_i_258_, lean_object* v_shift_259_){
_start:
{
size_t v_i_boxed_260_; size_t v_shift_boxed_261_; size_t v_res_262_; lean_object* v_r_263_; 
v_i_boxed_260_ = lean_unbox_usize(v_i_258_);
lean_dec(v_i_258_);
v_shift_boxed_261_ = lean_unbox_usize(v_shift_259_);
lean_dec(v_shift_259_);
v_res_262_ = l_Lean_PersistentHashMap_mul2Shift(v_i_boxed_260_, v_shift_boxed_261_);
v_r_263_ = lean_box_usize(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_div2Shift(size_t v_i_264_, size_t v_shift_265_){
_start:
{
size_t v___x_266_; 
v___x_266_ = lean_usize_shift_right(v_i_264_, v_shift_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_div2Shift___boxed(lean_object* v_i_267_, lean_object* v_shift_268_){
_start:
{
size_t v_i_boxed_269_; size_t v_shift_boxed_270_; size_t v_res_271_; lean_object* v_r_272_; 
v_i_boxed_269_ = lean_unbox_usize(v_i_267_);
lean_dec(v_i_267_);
v_shift_boxed_270_ = lean_unbox_usize(v_shift_268_);
lean_dec(v_shift_268_);
v_res_271_ = l_Lean_PersistentHashMap_div2Shift(v_i_boxed_269_, v_shift_boxed_270_);
v_r_272_ = lean_box_usize(v_res_271_);
return v_r_272_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_mod2Shift(size_t v_i_273_, size_t v_shift_274_){
_start:
{
size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; 
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_shift_left(v___x_275_, v_shift_274_);
v___x_277_ = lean_usize_sub(v___x_276_, v___x_275_);
v___x_278_ = lean_usize_land(v_i_273_, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mod2Shift___boxed(lean_object* v_i_279_, lean_object* v_shift_280_){
_start:
{
size_t v_i_boxed_281_; size_t v_shift_boxed_282_; size_t v_res_283_; lean_object* v_r_284_; 
v_i_boxed_281_ = lean_unbox_usize(v_i_279_);
lean_dec(v_i_279_);
v_shift_boxed_282_ = lean_unbox_usize(v_shift_280_);
lean_dec(v_shift_280_);
v_res_283_ = l_Lean_PersistentHashMap_mod2Shift(v_i_boxed_281_, v_shift_boxed_282_);
v_r_284_ = lean_box_usize(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(lean_object* v_inst_285_, lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_ks_290_; lean_object* v_vs_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_316_; 
v_ks_290_ = lean_ctor_get(v_x_286_, 0);
v_vs_291_ = lean_ctor_get(v_x_286_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_x_286_);
if (v_isSharedCheck_316_ == 0)
{
v___x_293_ = v_x_286_;
v_isShared_294_ = v_isSharedCheck_316_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_vs_291_);
lean_inc(v_ks_290_);
lean_dec(v_x_286_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_316_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_array_get_size(v_ks_290_);
v___x_296_ = lean_nat_dec_lt(v_x_287_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
lean_dec(v_x_287_);
lean_dec_ref(v_inst_285_);
v___x_297_ = lean_array_push(v_ks_290_, v_x_288_);
v___x_298_ = lean_array_push(v_vs_291_, v_x_289_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_298_);
lean_ctor_set(v___x_293_, 0, v___x_297_);
v___x_300_ = v___x_293_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
else
{
lean_object* v_k_x27_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_k_x27_302_ = lean_array_fget_borrowed(v_ks_290_, v_x_287_);
lean_inc_ref(v_inst_285_);
lean_inc(v_k_x27_302_);
lean_inc(v_x_288_);
v___x_303_ = lean_apply_2(v_inst_285_, v_x_288_, v_k_x27_302_);
v___x_304_ = lean_unbox(v___x_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_306_; 
if (v_isShared_294_ == 0)
{
v___x_306_ = v___x_293_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_ks_290_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_vs_291_);
v___x_306_ = v_reuseFailAlloc_310_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_x_287_, v___x_307_);
lean_dec(v_x_287_);
v_x_286_ = v___x_306_;
v_x_287_ = v___x_308_;
goto _start;
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_314_; 
lean_dec_ref(v_inst_285_);
v___x_311_ = lean_array_fset(v_ks_290_, v_x_287_, v_x_288_);
v___x_312_ = lean_array_fset(v_vs_291_, v_x_287_, v_x_289_);
lean_dec(v_x_287_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_312_);
lean_ctor_set(v___x_293_, 0, v___x_311_);
v___x_314_ = v___x_293_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_311_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux(lean_object* v_00_u03b1_317_, lean_object* v_00_u03b2_318_, lean_object* v_inst_319_, lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(v_inst_319_, v_x_320_, v_x_321_, v_x_322_, v_x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(lean_object* v_inst_325_, lean_object* v_n_326_, lean_object* v_k_327_, lean_object* v_v_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(v_inst_325_, v_n_326_, v___x_329_, v_k_327_, v_v_328_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode(lean_object* v_00_u03b1_331_, lean_object* v_00_u03b2_332_, lean_object* v_inst_333_, lean_object* v_n_334_, lean_object* v_k_335_, lean_object* v_v_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(v_inst_333_, v_n_334_, v_k_335_, v_v_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object* v_x_338_){
_start:
{
lean_object* v_ks_339_; lean_object* v___x_340_; 
v_ks_339_ = lean_ctor_get(v_x_338_, 0);
v___x_340_ = lean_array_get_size(v_ks_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg___boxed(lean_object* v_x_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_341_);
lean_dec_ref(v_x_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_x_345_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___boxed(lean_object* v_00_u03b1_347_, lean_object* v_00_u03b2_348_, lean_object* v_x_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_PersistentHashMap_getCollisionNodeSize(v_00_u03b1_347_, v_00_u03b2_348_, v_x_349_);
lean_dec_ref(v_x_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object* v_k_u2081_351_, lean_object* v_v_u2081_352_, lean_object* v_k_u2082_353_, lean_object* v_v_u2082_354_){
_start:
{
lean_object* v___x_355_; lean_object* v_ks_356_; lean_object* v___x_357_; lean_object* v_ks_358_; lean_object* v___x_359_; lean_object* v_vs_360_; lean_object* v___x_361_; 
v___x_355_ = lean_unsigned_to_nat(4u);
v_ks_356_ = lean_mk_empty_array_with_capacity(v___x_355_);
lean_inc_ref(v_ks_356_);
v___x_357_ = lean_array_push(v_ks_356_, v_k_u2081_351_);
v_ks_358_ = lean_array_push(v___x_357_, v_k_u2082_353_);
v___x_359_ = lean_array_push(v_ks_356_, v_v_u2081_352_);
v_vs_360_ = lean_array_push(v___x_359_, v_v_u2082_354_);
v___x_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_361_, 0, v_ks_358_);
lean_ctor_set(v___x_361_, 1, v_vs_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode(lean_object* v_00_u03b1_362_, lean_object* v_00_u03b2_363_, lean_object* v_k_u2081_364_, lean_object* v_v_u2081_365_, lean_object* v_k_u2082_366_, lean_object* v_v_u2082_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_k_u2081_364_, v_v_u2081_365_, v_k_u2082_366_, v_v_u2082_367_);
return v___x_368_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__0(void){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg(lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_x_372_, size_t v_x_373_, size_t v_x_374_, lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
lean_object* v_es_377_; size_t v___x_378_; size_t v___x_379_; lean_object* v_j_380_; lean_object* v___x_381_; uint8_t v___x_382_; 
v_es_377_ = lean_ctor_get(v_x_372_, 0);
v___x_378_ = ((size_t)31ULL);
v___x_379_ = lean_usize_land(v_x_373_, v___x_378_);
v_j_380_ = lean_usize_to_nat(v___x_379_);
v___x_381_ = lean_array_get_size(v_es_377_);
v___x_382_ = lean_nat_dec_lt(v_j_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_dec(v_j_380_);
lean_dec(v_x_376_);
lean_dec(v_x_375_);
lean_dec_ref(v_inst_371_);
lean_dec_ref(v_inst_370_);
return v_x_372_;
}
else
{
lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_422_; 
lean_inc_ref(v_es_377_);
v_isSharedCheck_422_ = !lean_is_exclusive(v_x_372_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v_x_372_, 0);
lean_dec(v_unused_423_);
v___x_384_ = v_x_372_;
v_isShared_385_ = v_isSharedCheck_422_;
goto v_resetjp_383_;
}
else
{
lean_dec(v_x_372_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_422_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v_v_386_; lean_object* v___x_387_; lean_object* v_xs_x27_388_; lean_object* v___y_390_; 
v_v_386_ = lean_array_fget(v_es_377_, v_j_380_);
v___x_387_ = lean_box(0);
v_xs_x27_388_ = lean_array_fset(v_es_377_, v_j_380_, v___x_387_);
switch(lean_obj_tag(v_v_386_))
{
case 0:
{
lean_object* v_key_395_; lean_object* v_val_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_407_; 
lean_dec_ref(v_inst_371_);
v_key_395_ = lean_ctor_get(v_v_386_, 0);
v_val_396_ = lean_ctor_get(v_v_386_, 1);
v_isSharedCheck_407_ = !lean_is_exclusive(v_v_386_);
if (v_isSharedCheck_407_ == 0)
{
v___x_398_ = v_v_386_;
v_isShared_399_ = v_isSharedCheck_407_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_val_396_);
lean_inc(v_key_395_);
lean_dec(v_v_386_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_407_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; uint8_t v___x_401_; 
lean_inc(v_key_395_);
lean_inc(v_x_375_);
v___x_400_ = lean_apply_2(v_inst_370_, v_x_375_, v_key_395_);
v___x_401_ = lean_unbox(v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_del_object(v___x_398_);
v___x_402_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_395_, v_val_396_, v_x_375_, v_x_376_);
v___x_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
v___y_390_ = v___x_403_;
goto v___jp_389_;
}
else
{
lean_object* v___x_405_; 
lean_dec(v_val_396_);
lean_dec(v_key_395_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v_x_376_);
lean_ctor_set(v___x_398_, 0, v_x_375_);
v___x_405_ = v___x_398_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_x_375_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v_x_376_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
v___y_390_ = v___x_405_;
goto v___jp_389_;
}
}
}
}
case 1:
{
lean_object* v_node_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_420_; 
v_node_408_ = lean_ctor_get(v_v_386_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v_v_386_);
if (v_isSharedCheck_420_ == 0)
{
v___x_410_ = v_v_386_;
v_isShared_411_ = v_isSharedCheck_420_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_node_408_);
lean_dec(v_v_386_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_420_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_412_ = ((size_t)5ULL);
v___x_413_ = lean_usize_shift_right(v_x_373_, v___x_412_);
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_x_374_, v___x_414_);
v___x_416_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_370_, v_inst_371_, v_node_408_, v___x_413_, v___x_415_, v_x_375_, v_x_376_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_416_);
v___x_418_ = v___x_410_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
v___y_390_ = v___x_418_;
goto v___jp_389_;
}
}
}
default: 
{
lean_object* v___x_421_; 
lean_dec_ref(v_inst_371_);
lean_dec_ref(v_inst_370_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_x_375_);
lean_ctor_set(v___x_421_, 1, v_x_376_);
v___y_390_ = v___x_421_;
goto v___jp_389_;
}
}
v___jp_389_:
{
lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_391_ = lean_array_fset(v_xs_x27_388_, v_j_380_, v___y_390_);
lean_dec(v_j_380_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_391_);
v___x_393_ = v___x_384_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
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
else
{
lean_object* v_ks_424_; lean_object* v_vs_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_445_; 
v_ks_424_ = lean_ctor_get(v_x_372_, 0);
v_vs_425_ = lean_ctor_get(v_x_372_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_372_);
if (v_isSharedCheck_445_ == 0)
{
v___x_427_ = v_x_372_;
v_isShared_428_ = v_isSharedCheck_445_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_vs_425_);
lean_inc(v_ks_424_);
lean_dec(v_x_372_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_445_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_ks_424_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_vs_425_);
v___x_430_ = v_reuseFailAlloc_444_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
lean_object* v_newNode_431_; uint8_t v___y_433_; size_t v___x_439_; uint8_t v___x_440_; 
lean_inc_ref(v_inst_370_);
v_newNode_431_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(v_inst_370_, v___x_430_, v_x_375_, v_x_376_);
v___x_439_ = ((size_t)7ULL);
v___x_440_ = lean_usize_dec_le(v___x_439_, v_x_374_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_431_);
v___x_442_ = lean_unsigned_to_nat(4u);
v___x_443_ = lean_nat_dec_lt(v___x_441_, v___x_442_);
lean_dec(v___x_441_);
v___y_433_ = v___x_443_;
goto v___jp_432_;
}
else
{
v___y_433_ = v___x_440_;
goto v___jp_432_;
}
v___jp_432_:
{
if (v___y_433_ == 0)
{
lean_object* v_ks_434_; lean_object* v_vs_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_ks_434_ = lean_ctor_get(v_newNode_431_, 0);
lean_inc_ref(v_ks_434_);
v_vs_435_ = lean_ctor_get(v_newNode_431_, 1);
lean_inc_ref(v_vs_435_);
lean_dec_ref(v_newNode_431_);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__0);
v___x_438_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_370_, v_inst_371_, v_x_374_, v_ks_434_, v_vs_435_, v___x_436_, v___x_437_);
lean_dec_ref(v_vs_435_);
lean_dec_ref(v_ks_434_);
return v___x_438_;
}
else
{
lean_dec_ref(v_inst_371_);
lean_dec_ref(v_inst_370_);
return v_newNode_431_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(lean_object* v_inst_446_, lean_object* v_inst_447_, size_t v_depth_448_, lean_object* v_keys_449_, lean_object* v_vals_450_, lean_object* v_i_451_, lean_object* v_entries_452_){
_start:
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_array_get_size(v_keys_449_);
v___x_454_ = lean_nat_dec_lt(v_i_451_, v___x_453_);
if (v___x_454_ == 0)
{
lean_dec(v_i_451_);
lean_dec_ref(v_inst_447_);
lean_dec_ref(v_inst_446_);
return v_entries_452_;
}
else
{
lean_object* v_k_455_; lean_object* v_v_456_; lean_object* v___x_457_; uint64_t v___x_458_; size_t v_h_459_; size_t v___x_460_; lean_object* v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; size_t v_h_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_k_455_ = lean_array_fget_borrowed(v_keys_449_, v_i_451_);
v_v_456_ = lean_array_fget_borrowed(v_vals_450_, v_i_451_);
lean_inc_ref_n(v_inst_447_, 2);
lean_inc_n(v_k_455_, 2);
v___x_457_ = lean_apply_1(v_inst_447_, v_k_455_);
v___x_458_ = lean_unbox_uint64(v___x_457_);
lean_dec_ref(v___x_457_);
v_h_459_ = lean_uint64_to_usize(v___x_458_);
v___x_460_ = ((size_t)5ULL);
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_sub(v_depth_448_, v___x_462_);
v___x_464_ = lean_usize_mul(v___x_460_, v___x_463_);
v_h_465_ = lean_usize_shift_right(v_h_459_, v___x_464_);
v___x_466_ = lean_nat_add(v_i_451_, v___x_461_);
lean_dec(v_i_451_);
lean_inc(v_v_456_);
lean_inc_ref(v_inst_446_);
v___x_467_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_446_, v_inst_447_, v_entries_452_, v_h_465_, v_depth_448_, v_k_455_, v_v_456_);
v_i_451_ = v___x_466_;
v_entries_452_ = v___x_467_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg___boxed(lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_depth_471_, lean_object* v_keys_472_, lean_object* v_vals_473_, lean_object* v_i_474_, lean_object* v_entries_475_){
_start:
{
size_t v_depth_boxed_476_; lean_object* v_res_477_; 
v_depth_boxed_476_ = lean_unbox_usize(v_depth_471_);
lean_dec(v_depth_471_);
v_res_477_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_469_, v_inst_470_, v_depth_boxed_476_, v_keys_472_, v_vals_473_, v_i_474_, v_entries_475_);
lean_dec_ref(v_vals_473_);
lean_dec_ref(v_keys_472_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg___boxed(lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
size_t v_x_461__boxed_485_; size_t v_x_462__boxed_486_; lean_object* v_res_487_; 
v_x_461__boxed_485_ = lean_unbox_usize(v_x_481_);
lean_dec(v_x_481_);
v_x_462__boxed_486_ = lean_unbox_usize(v_x_482_);
lean_dec(v_x_482_);
v_res_487_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_478_, v_inst_479_, v_x_480_, v_x_461__boxed_485_, v_x_462__boxed_486_, v_x_483_, v_x_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(lean_object* v_00_u03b1_488_, lean_object* v_00_u03b2_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, size_t v_depth_492_, lean_object* v_keys_493_, lean_object* v_vals_494_, lean_object* v_heq_495_, lean_object* v_i_496_, lean_object* v_entries_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_490_, v_inst_491_, v_depth_492_, v_keys_493_, v_vals_494_, v_i_496_, v_entries_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___boxed(lean_object* v_00_u03b1_499_, lean_object* v_00_u03b2_500_, lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_depth_503_, lean_object* v_keys_504_, lean_object* v_vals_505_, lean_object* v_heq_506_, lean_object* v_i_507_, lean_object* v_entries_508_){
_start:
{
size_t v_depth_boxed_509_; lean_object* v_res_510_; 
v_depth_boxed_509_ = lean_unbox_usize(v_depth_503_);
lean_dec(v_depth_503_);
v_res_510_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(v_00_u03b1_499_, v_00_u03b2_500_, v_inst_501_, v_inst_502_, v_depth_boxed_509_, v_keys_504_, v_vals_505_, v_heq_506_, v_i_507_, v_entries_508_);
lean_dec_ref(v_vals_505_);
lean_dec_ref(v_keys_504_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux(lean_object* v_00_u03b1_511_, lean_object* v_00_u03b2_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_x_515_, size_t v_x_516_, size_t v_x_517_, lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_513_, v_inst_514_, v_x_515_, v_x_516_, v_x_517_, v_x_518_, v_x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___boxed(lean_object* v_00_u03b1_521_, lean_object* v_00_u03b2_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_x_525_, lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
size_t v_x_639__boxed_530_; size_t v_x_640__boxed_531_; lean_object* v_res_532_; 
v_x_639__boxed_530_ = lean_unbox_usize(v_x_526_);
lean_dec(v_x_526_);
v_x_640__boxed_531_ = lean_unbox_usize(v_x_527_);
lean_dec(v_x_527_);
v_res_532_ = l_Lean_PersistentHashMap_insertAux(v_00_u03b1_521_, v_00_u03b2_522_, v_inst_523_, v_inst_524_, v_x_525_, v_x_639__boxed_530_, v_x_640__boxed_531_, v_x_528_, v_x_529_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v___x_538_; uint64_t v___x_539_; size_t v___x_540_; size_t v___x_541_; lean_object* v___x_542_; 
lean_inc_ref(v_x_534_);
lean_inc(v_x_536_);
v___x_538_ = lean_apply_1(v_x_534_, v_x_536_);
v___x_539_ = lean_unbox_uint64(v___x_538_);
lean_dec_ref(v___x_538_);
v___x_540_ = lean_uint64_to_usize(v___x_539_);
v___x_541_ = ((size_t)1ULL);
v___x_542_ = l_Lean_PersistentHashMap_insertAux___redArg(v_x_533_, v_x_534_, v_x_535_, v___x_540_, v___x_541_, v_x_536_, v_x_537_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_PersistentHashMap_insert___redArg(v_x_545_, v_x_546_, v_x_547_, v_x_548_, v_x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg(lean_object* v_inst_551_, lean_object* v_keys_552_, lean_object* v_vals_553_, lean_object* v_i_554_, lean_object* v_k_555_){
_start:
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_array_get_size(v_keys_552_);
v___x_557_ = lean_nat_dec_lt(v_i_554_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; 
lean_dec(v_k_555_);
lean_dec(v_i_554_);
lean_dec_ref(v_inst_551_);
v___x_558_ = lean_box(0);
return v___x_558_;
}
else
{
lean_object* v_k_x27_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_k_x27_559_ = lean_array_fget_borrowed(v_keys_552_, v_i_554_);
lean_inc_ref(v_inst_551_);
lean_inc(v_k_x27_559_);
lean_inc(v_k_555_);
v___x_560_ = lean_apply_2(v_inst_551_, v_k_555_, v_k_x27_559_);
v___x_561_ = lean_unbox(v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_i_554_, v___x_562_);
lean_dec(v_i_554_);
v_i_554_ = v___x_563_;
goto _start;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v_k_555_);
lean_dec_ref(v_inst_551_);
v___x_565_ = lean_array_fget_borrowed(v_vals_553_, v_i_554_);
lean_dec(v_i_554_);
lean_inc(v___x_565_);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg___boxed(lean_object* v_inst_567_, lean_object* v_keys_568_, lean_object* v_vals_569_, lean_object* v_i_570_, lean_object* v_k_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_567_, v_keys_568_, v_vals_569_, v_i_570_, v_k_571_);
lean_dec_ref(v_vals_569_);
lean_dec_ref(v_keys_568_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux(lean_object* v_00_u03b1_573_, lean_object* v_00_u03b2_574_, lean_object* v_inst_575_, lean_object* v_keys_576_, lean_object* v_vals_577_, lean_object* v_heq_578_, lean_object* v_i_579_, lean_object* v_k_580_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_575_, v_keys_576_, v_vals_577_, v_i_579_, v_k_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___boxed(lean_object* v_00_u03b1_582_, lean_object* v_00_u03b2_583_, lean_object* v_inst_584_, lean_object* v_keys_585_, lean_object* v_vals_586_, lean_object* v_heq_587_, lean_object* v_i_588_, lean_object* v_k_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_PersistentHashMap_findAtAux(v_00_u03b1_582_, v_00_u03b2_583_, v_inst_584_, v_keys_585_, v_vals_586_, v_heq_587_, v_i_588_, v_k_589_);
lean_dec_ref(v_vals_586_);
lean_dec_ref(v_keys_585_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg(lean_object* v_inst_591_, lean_object* v_x_592_, size_t v_x_593_, lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_592_) == 0)
{
lean_object* v_es_595_; lean_object* v___x_596_; size_t v___x_597_; size_t v___x_598_; lean_object* v_j_599_; lean_object* v___x_600_; 
v_es_595_ = lean_ctor_get(v_x_592_, 0);
lean_inc_ref(v_es_595_);
lean_dec_ref_known(v_x_592_, 1);
v___x_596_ = lean_box(2);
v___x_597_ = ((size_t)31ULL);
v___x_598_ = lean_usize_land(v_x_593_, v___x_597_);
v_j_599_ = lean_usize_to_nat(v___x_598_);
v___x_600_ = lean_array_get(v___x_596_, v_es_595_, v_j_599_);
lean_dec(v_j_599_);
lean_dec_ref(v_es_595_);
switch(lean_obj_tag(v___x_600_))
{
case 0:
{
lean_object* v_key_601_; lean_object* v_val_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_key_601_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_key_601_);
v_val_602_ = lean_ctor_get(v___x_600_, 1);
lean_inc(v_val_602_);
lean_dec_ref_known(v___x_600_, 2);
v___x_603_ = lean_apply_2(v_inst_591_, v_x_594_, v_key_601_);
v___x_604_ = lean_unbox(v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_dec(v_val_602_);
v___x_605_ = lean_box(0);
return v___x_605_;
}
else
{
lean_object* v___x_606_; 
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v_val_602_);
return v___x_606_;
}
}
case 1:
{
lean_object* v_node_607_; size_t v___x_608_; size_t v___x_609_; 
v_node_607_ = lean_ctor_get(v___x_600_, 0);
lean_inc(v_node_607_);
lean_dec_ref_known(v___x_600_, 1);
v___x_608_ = ((size_t)5ULL);
v___x_609_ = lean_usize_shift_right(v_x_593_, v___x_608_);
v_x_592_ = v_node_607_;
v_x_593_ = v___x_609_;
goto _start;
}
default: 
{
lean_object* v___x_611_; 
lean_dec(v_x_594_);
lean_dec_ref(v_inst_591_);
v___x_611_ = lean_box(0);
return v___x_611_;
}
}
}
else
{
lean_object* v_ks_612_; lean_object* v_vs_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v_ks_612_ = lean_ctor_get(v_x_592_, 0);
lean_inc_ref(v_ks_612_);
v_vs_613_ = lean_ctor_get(v_x_592_, 1);
lean_inc_ref(v_vs_613_);
lean_dec_ref_known(v_x_592_, 2);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_591_, v_ks_612_, v_vs_613_, v___x_614_, v_x_594_);
lean_dec_ref(v_vs_613_);
lean_dec_ref(v_ks_612_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg___boxed(lean_object* v_inst_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
size_t v_x_143__boxed_620_; lean_object* v_res_621_; 
v_x_143__boxed_620_ = lean_unbox_usize(v_x_618_);
lean_dec(v_x_618_);
v_res_621_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_616_, v_x_617_, v_x_143__boxed_620_, v_x_619_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux(lean_object* v_00_u03b1_622_, lean_object* v_00_u03b2_623_, lean_object* v_inst_624_, lean_object* v_x_625_, size_t v_x_626_, lean_object* v_x_627_){
_start:
{
lean_object* v___x_628_; 
lean_inc_ref(v_x_625_);
v___x_628_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_624_, v_x_625_, v_x_626_, v_x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___boxed(lean_object* v_00_u03b1_629_, lean_object* v_00_u03b2_630_, lean_object* v_inst_631_, lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
size_t v_x_195__boxed_635_; lean_object* v_res_636_; 
v_x_195__boxed_635_ = lean_unbox_usize(v_x_633_);
lean_dec(v_x_633_);
v_res_636_ = l_Lean_PersistentHashMap_findAux(v_00_u03b1_629_, v_00_u03b2_630_, v_inst_631_, v_x_632_, v_x_195__boxed_635_, v_x_634_);
lean_dec_ref(v_x_632_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
lean_object* v___x_641_; uint64_t v___x_642_; size_t v___x_643_; lean_object* v___x_644_; 
lean_inc(v_x_640_);
v___x_641_ = lean_apply_1(v_x_638_, v_x_640_);
v___x_642_ = lean_unbox_uint64(v___x_641_);
lean_dec_ref(v___x_641_);
v___x_643_ = lean_uint64_to_usize(v___x_642_);
lean_inc_ref(v_x_639_);
v___x_644_ = l_Lean_PersistentHashMap_findAux___redArg(v_x_637_, v_x_639_, v___x_643_, v_x_640_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg___boxed(lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_645_, v_x_646_, v_x_647_, v_x_648_);
lean_dec_ref(v_x_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f(lean_object* v_00_u03b1_650_, lean_object* v_00_u03b2_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_652_, v_x_653_, v_x_654_, v_x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___boxed(lean_object* v_00_u03b1_657_, lean_object* v_00_u03b2_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_PersistentHashMap_find_x3f(v_00_u03b1_657_, v_00_u03b2_658_, v_x_659_, v_x_660_, v_x_661_, v_x_662_);
lean_dec_ref(v_x_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_m_666_, lean_object* v_i_667_, lean_object* v_x_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_664_, v_x_665_, v_m_666_, v_i_667_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed(lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_m_672_, lean_object* v_i_673_, lean_object* v_x_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(v_x_670_, v_x_671_, v_m_672_, v_i_673_, v_x_674_);
lean_dec_ref(v_m_672_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg(lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
lean_object* v___f_678_; 
v___f_678_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_678_, 0, v_x_676_);
lean_closure_set(v___f_678_, 1, v_x_677_);
return v___f_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue(lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
lean_object* v___f_683_; 
v___f_683_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_683_, 0, v_x_681_);
lean_closure_set(v___f_683_, 1, v_x_682_);
return v___f_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg(lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_m_686_, lean_object* v_a_687_, lean_object* v_b_u2080_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_684_, v_x_685_, v_m_686_, v_a_687_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_inc(v_b_u2080_688_);
return v_b_u2080_688_;
}
else
{
lean_object* v_val_690_; 
v_val_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v___x_689_, 1);
return v_val_690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg___boxed(lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_m_693_, lean_object* v_a_694_, lean_object* v_b_u2080_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_PersistentHashMap_findD___redArg(v_x_691_, v_x_692_, v_m_693_, v_a_694_, v_b_u2080_695_);
lean_dec(v_b_u2080_695_);
lean_dec_ref(v_m_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD(lean_object* v_00_u03b1_697_, lean_object* v_00_u03b2_698_, lean_object* v_x_699_, lean_object* v_x_700_, lean_object* v_m_701_, lean_object* v_a_702_, lean_object* v_b_u2080_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_699_, v_x_700_, v_m_701_, v_a_702_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_inc(v_b_u2080_703_);
return v_b_u2080_703_;
}
else
{
lean_object* v_val_705_; 
v_val_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v___x_704_, 1);
return v_val_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___boxed(lean_object* v_00_u03b1_706_, lean_object* v_00_u03b2_707_, lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_m_710_, lean_object* v_a_711_, lean_object* v_b_u2080_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_PersistentHashMap_findD(v_00_u03b1_706_, v_00_u03b2_707_, v_x_708_, v_x_709_, v_m_710_, v_a_711_, v_b_u2080_712_);
lean_dec(v_b_u2080_712_);
lean_dec_ref(v_m_710_);
return v_res_713_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_717_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__2));
v___x_718_ = lean_unsigned_to_nat(14u);
v___x_719_ = lean_unsigned_to_nat(178u);
v___x_720_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__1));
v___x_721_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__0));
v___x_722_ = l_mkPanicMessageWithDecl(v___x_721_, v___x_720_, v___x_719_, v___x_718_, v___x_717_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg(lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_inst_725_, lean_object* v_m_726_, lean_object* v_a_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_723_, v_x_724_, v_m_726_, v_a_727_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_730_ = l_panic___redArg(v_inst_725_, v___x_729_);
return v___x_730_;
}
else
{
lean_object* v_val_731_; 
v_val_731_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_val_731_);
lean_dec_ref_known(v___x_728_, 1);
return v_val_731_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg___boxed(lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_inst_734_, lean_object* v_m_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_PersistentHashMap_find_x21___redArg(v_x_732_, v_x_733_, v_inst_734_, v_m_735_, v_a_736_);
lean_dec_ref(v_m_735_);
lean_dec(v_inst_734_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21(lean_object* v_00_u03b1_738_, lean_object* v_00_u03b2_739_, lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_inst_742_, lean_object* v_m_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_740_, v_x_741_, v_m_743_, v_a_744_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_747_ = l_panic___redArg(v_inst_742_, v___x_746_);
return v___x_747_;
}
else
{
lean_object* v_val_748_; 
v_val_748_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_748_);
lean_dec_ref_known(v___x_745_, 1);
return v_val_748_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___boxed(lean_object* v_00_u03b1_749_, lean_object* v_00_u03b2_750_, lean_object* v_x_751_, lean_object* v_x_752_, lean_object* v_inst_753_, lean_object* v_m_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_PersistentHashMap_find_x21(v_00_u03b1_749_, v_00_u03b2_750_, v_x_751_, v_x_752_, v_inst_753_, v_m_754_, v_a_755_);
lean_dec_ref(v_m_754_);
lean_dec(v_inst_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg(lean_object* v_inst_757_, lean_object* v_keys_758_, lean_object* v_vals_759_, lean_object* v_i_760_, lean_object* v_k_761_){
_start:
{
lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_762_ = lean_array_get_size(v_keys_758_);
v___x_763_ = lean_nat_dec_lt(v_i_760_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; 
lean_dec(v_k_761_);
lean_dec(v_i_760_);
lean_dec_ref(v_inst_757_);
v___x_764_ = lean_box(0);
return v___x_764_;
}
else
{
lean_object* v_k_x27_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_k_x27_765_ = lean_array_fget_borrowed(v_keys_758_, v_i_760_);
lean_inc_ref(v_inst_757_);
lean_inc(v_k_x27_765_);
lean_inc(v_k_761_);
v___x_766_ = lean_apply_2(v_inst_757_, v_k_761_, v_k_x27_765_);
v___x_767_ = lean_unbox(v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_add(v_i_760_, v___x_768_);
lean_dec(v_i_760_);
v_i_760_ = v___x_769_;
goto _start;
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec(v_k_761_);
lean_dec_ref(v_inst_757_);
v___x_771_ = lean_array_fget_borrowed(v_vals_759_, v_i_760_);
lean_dec(v_i_760_);
lean_inc(v___x_771_);
lean_inc(v_k_x27_765_);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v_k_x27_765_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg___boxed(lean_object* v_inst_774_, lean_object* v_keys_775_, lean_object* v_vals_776_, lean_object* v_i_777_, lean_object* v_k_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_774_, v_keys_775_, v_vals_776_, v_i_777_, v_k_778_);
lean_dec_ref(v_vals_776_);
lean_dec_ref(v_keys_775_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux(lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_inst_782_, lean_object* v_keys_783_, lean_object* v_vals_784_, lean_object* v_heq_785_, lean_object* v_i_786_, lean_object* v_k_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_782_, v_keys_783_, v_vals_784_, v_i_786_, v_k_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___boxed(lean_object* v_00_u03b1_789_, lean_object* v_00_u03b2_790_, lean_object* v_inst_791_, lean_object* v_keys_792_, lean_object* v_vals_793_, lean_object* v_heq_794_, lean_object* v_i_795_, lean_object* v_k_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_PersistentHashMap_findEntryAtAux(v_00_u03b1_789_, v_00_u03b2_790_, v_inst_791_, v_keys_792_, v_vals_793_, v_heq_794_, v_i_795_, v_k_796_);
lean_dec_ref(v_vals_793_);
lean_dec_ref(v_keys_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg(lean_object* v_inst_798_, lean_object* v_x_799_, size_t v_x_800_, lean_object* v_x_801_){
_start:
{
if (lean_obj_tag(v_x_799_) == 0)
{
lean_object* v_es_802_; lean_object* v___x_803_; size_t v___x_804_; size_t v___x_805_; lean_object* v_j_806_; lean_object* v___x_807_; 
v_es_802_ = lean_ctor_get(v_x_799_, 0);
lean_inc_ref(v_es_802_);
lean_dec_ref_known(v_x_799_, 1);
v___x_803_ = lean_box(2);
v___x_804_ = ((size_t)31ULL);
v___x_805_ = lean_usize_land(v_x_800_, v___x_804_);
v_j_806_ = lean_usize_to_nat(v___x_805_);
v___x_807_ = lean_array_get(v___x_803_, v_es_802_, v_j_806_);
lean_dec(v_j_806_);
lean_dec_ref(v_es_802_);
switch(lean_obj_tag(v___x_807_))
{
case 0:
{
lean_object* v_key_808_; lean_object* v_val_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v_key_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc_n(v_key_808_, 2);
v_val_809_ = lean_ctor_get(v___x_807_, 1);
lean_inc(v_val_809_);
lean_dec_ref_known(v___x_807_, 2);
v___x_810_ = lean_apply_2(v_inst_798_, v_x_801_, v_key_808_);
v___x_811_ = lean_unbox(v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
lean_dec(v_val_809_);
lean_dec(v_key_808_);
v___x_812_ = lean_box(0);
return v___x_812_;
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v_key_808_);
lean_ctor_set(v___x_813_, 1, v_val_809_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
return v___x_814_;
}
}
case 1:
{
lean_object* v_node_815_; size_t v___x_816_; size_t v___x_817_; 
v_node_815_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_node_815_);
lean_dec_ref_known(v___x_807_, 1);
v___x_816_ = ((size_t)5ULL);
v___x_817_ = lean_usize_shift_right(v_x_800_, v___x_816_);
v_x_799_ = v_node_815_;
v_x_800_ = v___x_817_;
goto _start;
}
default: 
{
lean_object* v___x_819_; 
lean_dec(v_x_801_);
lean_dec_ref(v_inst_798_);
v___x_819_ = lean_box(0);
return v___x_819_;
}
}
}
else
{
lean_object* v_ks_820_; lean_object* v_vs_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_ks_820_ = lean_ctor_get(v_x_799_, 0);
lean_inc_ref(v_ks_820_);
v_vs_821_ = lean_ctor_get(v_x_799_, 1);
lean_inc_ref(v_vs_821_);
lean_dec_ref_known(v_x_799_, 2);
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_798_, v_ks_820_, v_vs_821_, v___x_822_, v_x_801_);
lean_dec_ref(v_vs_821_);
lean_dec_ref(v_ks_820_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg___boxed(lean_object* v_inst_824_, lean_object* v_x_825_, lean_object* v_x_826_, lean_object* v_x_827_){
_start:
{
size_t v_x_147__boxed_828_; lean_object* v_res_829_; 
v_x_147__boxed_828_ = lean_unbox_usize(v_x_826_);
lean_dec(v_x_826_);
v_res_829_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_824_, v_x_825_, v_x_147__boxed_828_, v_x_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux(lean_object* v_00_u03b1_830_, lean_object* v_00_u03b2_831_, lean_object* v_inst_832_, lean_object* v_x_833_, size_t v_x_834_, lean_object* v_x_835_){
_start:
{
lean_object* v___x_836_; 
lean_inc_ref(v_x_833_);
v___x_836_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_832_, v_x_833_, v_x_834_, v_x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___boxed(lean_object* v_00_u03b1_837_, lean_object* v_00_u03b2_838_, lean_object* v_inst_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
size_t v_x_201__boxed_843_; lean_object* v_res_844_; 
v_x_201__boxed_843_ = lean_unbox_usize(v_x_841_);
lean_dec(v_x_841_);
v_res_844_ = l_Lean_PersistentHashMap_findEntryAux(v_00_u03b1_837_, v_00_u03b2_838_, v_inst_839_, v_x_840_, v_x_201__boxed_843_, v_x_842_);
lean_dec_ref(v_x_840_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
lean_object* v___x_849_; uint64_t v___x_850_; size_t v___x_851_; lean_object* v___x_852_; 
lean_inc(v_x_848_);
v___x_849_ = lean_apply_1(v_x_846_, v_x_848_);
v___x_850_ = lean_unbox_uint64(v___x_849_);
lean_dec_ref(v___x_849_);
v___x_851_ = lean_uint64_to_usize(v___x_850_);
lean_inc_ref(v_x_847_);
v___x_852_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_x_845_, v_x_847_, v___x_851_, v_x_848_);
return v___x_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg___boxed(lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_x_855_, lean_object* v_x_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_853_, v_x_854_, v_x_855_, v_x_856_);
lean_dec_ref(v_x_855_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f(lean_object* v_00_u03b1_858_, lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
lean_object* v___x_864_; 
v___x_864_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_860_, v_x_861_, v_x_862_, v_x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___boxed(lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_PersistentHashMap_findEntry_x3f(v_00_u03b1_865_, v_00_u03b2_866_, v_x_867_, v_x_868_, v_x_869_, v_x_870_);
lean_dec_ref(v_x_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg(lean_object* v_inst_872_, lean_object* v_keys_873_, lean_object* v_i_874_, lean_object* v_k_875_, lean_object* v_k_u2080_876_){
_start:
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = lean_array_get_size(v_keys_873_);
v___x_878_ = lean_nat_dec_lt(v_i_874_, v___x_877_);
if (v___x_878_ == 0)
{
lean_dec(v_k_875_);
lean_dec(v_i_874_);
lean_dec_ref(v_inst_872_);
lean_inc(v_k_u2080_876_);
return v_k_u2080_876_;
}
else
{
lean_object* v_k_x27_879_; lean_object* v___x_880_; uint8_t v___x_881_; 
v_k_x27_879_ = lean_array_fget_borrowed(v_keys_873_, v_i_874_);
lean_inc_ref(v_inst_872_);
lean_inc(v_k_x27_879_);
lean_inc(v_k_875_);
v___x_880_ = lean_apply_2(v_inst_872_, v_k_875_, v_k_x27_879_);
v___x_881_ = lean_unbox(v___x_880_);
if (v___x_881_ == 0)
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = lean_nat_add(v_i_874_, v___x_882_);
lean_dec(v_i_874_);
v_i_874_ = v___x_883_;
goto _start;
}
else
{
lean_dec(v_k_875_);
lean_dec(v_i_874_);
lean_dec_ref(v_inst_872_);
lean_inc(v_k_x27_879_);
return v_k_x27_879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg___boxed(lean_object* v_inst_885_, lean_object* v_keys_886_, lean_object* v_i_887_, lean_object* v_k_888_, lean_object* v_k_u2080_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_885_, v_keys_886_, v_i_887_, v_k_888_, v_k_u2080_889_);
lean_dec(v_k_u2080_889_);
lean_dec_ref(v_keys_886_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_inst_893_, lean_object* v_keys_894_, lean_object* v_vals_895_, lean_object* v_heq_896_, lean_object* v_i_897_, lean_object* v_k_898_, lean_object* v_k_u2080_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_893_, v_keys_894_, v_i_897_, v_k_898_, v_k_u2080_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___boxed(lean_object* v_00_u03b1_901_, lean_object* v_00_u03b2_902_, lean_object* v_inst_903_, lean_object* v_keys_904_, lean_object* v_vals_905_, lean_object* v_heq_906_, lean_object* v_i_907_, lean_object* v_k_908_, lean_object* v_k_u2080_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_PersistentHashMap_findKeyDAtAux(v_00_u03b1_901_, v_00_u03b2_902_, v_inst_903_, v_keys_904_, v_vals_905_, v_heq_906_, v_i_907_, v_k_908_, v_k_u2080_909_);
lean_dec(v_k_u2080_909_);
lean_dec_ref(v_vals_905_);
lean_dec_ref(v_keys_904_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object* v_inst_911_, lean_object* v_x_912_, size_t v_x_913_, lean_object* v_x_914_, lean_object* v_x_915_){
_start:
{
if (lean_obj_tag(v_x_912_) == 0)
{
lean_object* v_es_916_; lean_object* v___x_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v_j_920_; lean_object* v___x_921_; 
v_es_916_ = lean_ctor_get(v_x_912_, 0);
lean_inc_ref(v_es_916_);
lean_dec_ref_known(v_x_912_, 1);
v___x_917_ = lean_box(2);
v___x_918_ = ((size_t)31ULL);
v___x_919_ = lean_usize_land(v_x_913_, v___x_918_);
v_j_920_ = lean_usize_to_nat(v___x_919_);
v___x_921_ = lean_array_get(v___x_917_, v_es_916_, v_j_920_);
lean_dec(v_j_920_);
lean_dec_ref(v_es_916_);
switch(lean_obj_tag(v___x_921_))
{
case 0:
{
lean_object* v_key_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_key_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc_n(v_key_922_, 2);
lean_dec_ref_known(v___x_921_, 2);
v___x_923_ = lean_apply_2(v_inst_911_, v_x_914_, v_key_922_);
v___x_924_ = lean_unbox(v___x_923_);
if (v___x_924_ == 0)
{
lean_dec(v_key_922_);
lean_inc(v_x_915_);
return v_x_915_;
}
else
{
return v_key_922_;
}
}
case 1:
{
lean_object* v_node_925_; size_t v___x_926_; size_t v___x_927_; 
v_node_925_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_node_925_);
lean_dec_ref_known(v___x_921_, 1);
v___x_926_ = ((size_t)5ULL);
v___x_927_ = lean_usize_shift_right(v_x_913_, v___x_926_);
v_x_912_ = v_node_925_;
v_x_913_ = v___x_927_;
goto _start;
}
default: 
{
lean_dec(v_x_914_);
lean_dec_ref(v_inst_911_);
lean_inc(v_x_915_);
return v_x_915_;
}
}
}
else
{
lean_object* v_ks_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_ks_929_ = lean_ctor_get(v_x_912_, 0);
lean_inc_ref(v_ks_929_);
lean_dec_ref_known(v_x_912_, 2);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_911_, v_ks_929_, v___x_930_, v_x_914_, v_x_915_);
lean_dec_ref(v_ks_929_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg___boxed(lean_object* v_inst_932_, lean_object* v_x_933_, lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
size_t v_x_132__boxed_937_; lean_object* v_res_938_; 
v_x_132__boxed_937_ = lean_unbox_usize(v_x_934_);
lean_dec(v_x_934_);
v_res_938_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_932_, v_x_933_, v_x_132__boxed_937_, v_x_935_, v_x_936_);
lean_dec(v_x_936_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux(lean_object* v_00_u03b1_939_, lean_object* v_00_u03b2_940_, lean_object* v_inst_941_, lean_object* v_x_942_, size_t v_x_943_, lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_941_, v_x_942_, v_x_943_, v_x_944_, v_x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___boxed(lean_object* v_00_u03b1_947_, lean_object* v_00_u03b2_948_, lean_object* v_inst_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_x_952_, lean_object* v_x_953_){
_start:
{
size_t v_x_179__boxed_954_; lean_object* v_res_955_; 
v_x_179__boxed_954_ = lean_unbox_usize(v_x_951_);
lean_dec(v_x_951_);
v_res_955_ = l_Lean_PersistentHashMap_findKeyDAux(v_00_u03b1_947_, v_00_u03b2_948_, v_inst_949_, v_x_950_, v_x_179__boxed_954_, v_x_952_, v_x_953_);
lean_dec(v_x_953_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg(lean_object* v_x_956_, lean_object* v_x_957_, lean_object* v_m_958_, lean_object* v_a_959_, lean_object* v_a_u2080_960_){
_start:
{
lean_object* v___x_961_; uint64_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; 
lean_inc(v_a_959_);
v___x_961_ = lean_apply_1(v_x_957_, v_a_959_);
v___x_962_ = lean_unbox_uint64(v___x_961_);
lean_dec_ref(v___x_961_);
v___x_963_ = lean_uint64_to_usize(v___x_962_);
v___x_964_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_956_, v_m_958_, v___x_963_, v_a_959_, v_a_u2080_960_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg___boxed(lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_m_967_, lean_object* v_a_968_, lean_object* v_a_u2080_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_PersistentHashMap_findKeyD___redArg(v_x_965_, v_x_966_, v_m_967_, v_a_968_, v_a_u2080_969_);
lean_dec(v_a_u2080_969_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD(lean_object* v_00_u03b1_971_, lean_object* v_00_u03b2_972_, lean_object* v_x_973_, lean_object* v_x_974_, lean_object* v_m_975_, lean_object* v_a_976_, lean_object* v_a_u2080_977_){
_start:
{
lean_object* v___x_978_; uint64_t v___x_979_; size_t v___x_980_; lean_object* v___x_981_; 
lean_inc(v_a_976_);
v___x_978_ = lean_apply_1(v_x_974_, v_a_976_);
v___x_979_ = lean_unbox_uint64(v___x_978_);
lean_dec_ref(v___x_978_);
v___x_980_ = lean_uint64_to_usize(v___x_979_);
v___x_981_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_973_, v_m_975_, v___x_980_, v_a_976_, v_a_u2080_977_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___boxed(lean_object* v_00_u03b1_982_, lean_object* v_00_u03b2_983_, lean_object* v_x_984_, lean_object* v_x_985_, lean_object* v_m_986_, lean_object* v_a_987_, lean_object* v_a_u2080_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Lean_PersistentHashMap_findKeyD(v_00_u03b1_982_, v_00_u03b2_983_, v_x_984_, v_x_985_, v_m_986_, v_a_987_, v_a_u2080_988_);
lean_dec(v_a_u2080_988_);
return v_res_989_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___redArg(lean_object* v_inst_990_, lean_object* v_keys_991_, lean_object* v_i_992_, lean_object* v_k_993_){
_start:
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_array_get_size(v_keys_991_);
v___x_995_ = lean_nat_dec_lt(v_i_992_, v___x_994_);
if (v___x_995_ == 0)
{
lean_dec(v_k_993_);
lean_dec(v_i_992_);
lean_dec_ref(v_inst_990_);
return v___x_995_;
}
else
{
lean_object* v_k_x27_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_k_x27_996_ = lean_array_fget_borrowed(v_keys_991_, v_i_992_);
lean_inc_ref(v_inst_990_);
lean_inc(v_k_x27_996_);
lean_inc(v_k_993_);
v___x_997_ = lean_apply_2(v_inst_990_, v_k_993_, v_k_x27_996_);
v___x_998_ = lean_unbox(v___x_997_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_unsigned_to_nat(1u);
v___x_1000_ = lean_nat_add(v_i_992_, v___x_999_);
lean_dec(v_i_992_);
v_i_992_ = v___x_1000_;
goto _start;
}
else
{
uint8_t v___x_1002_; 
lean_dec(v_k_993_);
lean_dec(v_i_992_);
lean_dec_ref(v_inst_990_);
v___x_1002_ = lean_unbox(v___x_997_);
return v___x_1002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___redArg___boxed(lean_object* v_inst_1003_, lean_object* v_keys_1004_, lean_object* v_i_1005_, lean_object* v_k_1006_){
_start:
{
uint8_t v_res_1007_; lean_object* v_r_1008_; 
v_res_1007_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1003_, v_keys_1004_, v_i_1005_, v_k_1006_);
lean_dec_ref(v_keys_1004_);
v_r_1008_ = lean_box(v_res_1007_);
return v_r_1008_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux(lean_object* v_00_u03b1_1009_, lean_object* v_00_u03b2_1010_, lean_object* v_inst_1011_, lean_object* v_keys_1012_, lean_object* v_vals_1013_, lean_object* v_heq_1014_, lean_object* v_i_1015_, lean_object* v_k_1016_){
_start:
{
uint8_t v___x_1017_; 
v___x_1017_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1011_, v_keys_1012_, v_i_1015_, v_k_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___boxed(lean_object* v_00_u03b1_1018_, lean_object* v_00_u03b2_1019_, lean_object* v_inst_1020_, lean_object* v_keys_1021_, lean_object* v_vals_1022_, lean_object* v_heq_1023_, lean_object* v_i_1024_, lean_object* v_k_1025_){
_start:
{
uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_res_1026_ = l_Lean_PersistentHashMap_containsAtAux(v_00_u03b1_1018_, v_00_u03b2_1019_, v_inst_1020_, v_keys_1021_, v_vals_1022_, v_heq_1023_, v_i_1024_, v_k_1025_);
lean_dec_ref(v_vals_1022_);
lean_dec_ref(v_keys_1021_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___redArg(lean_object* v_inst_1028_, lean_object* v_x_1029_, size_t v_x_1030_, lean_object* v_x_1031_){
_start:
{
if (lean_obj_tag(v_x_1029_) == 0)
{
lean_object* v_es_1032_; lean_object* v___x_1033_; size_t v___x_1034_; size_t v___x_1035_; lean_object* v_j_1036_; lean_object* v___x_1037_; 
v_es_1032_ = lean_ctor_get(v_x_1029_, 0);
lean_inc_ref(v_es_1032_);
lean_dec_ref_known(v_x_1029_, 1);
v___x_1033_ = lean_box(2);
v___x_1034_ = ((size_t)31ULL);
v___x_1035_ = lean_usize_land(v_x_1030_, v___x_1034_);
v_j_1036_ = lean_usize_to_nat(v___x_1035_);
v___x_1037_ = lean_array_get(v___x_1033_, v_es_1032_, v_j_1036_);
lean_dec(v_j_1036_);
lean_dec_ref(v_es_1032_);
switch(lean_obj_tag(v___x_1037_))
{
case 0:
{
lean_object* v_key_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_key_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_key_1038_);
lean_dec_ref_known(v___x_1037_, 2);
v___x_1039_ = lean_apply_2(v_inst_1028_, v_x_1031_, v_key_1038_);
v___x_1040_ = lean_unbox(v___x_1039_);
return v___x_1040_;
}
case 1:
{
lean_object* v_node_1041_; size_t v___x_1042_; size_t v___x_1043_; 
v_node_1041_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_node_1041_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1042_ = ((size_t)5ULL);
v___x_1043_ = lean_usize_shift_right(v_x_1030_, v___x_1042_);
v_x_1029_ = v_node_1041_;
v_x_1030_ = v___x_1043_;
goto _start;
}
default: 
{
uint8_t v___x_1045_; 
lean_dec(v_x_1031_);
lean_dec_ref(v_inst_1028_);
v___x_1045_ = 0;
return v___x_1045_;
}
}
}
else
{
lean_object* v_ks_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_ks_1046_ = lean_ctor_get(v_x_1029_, 0);
lean_inc_ref(v_ks_1046_);
lean_dec_ref_known(v_x_1029_, 2);
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1028_, v_ks_1046_, v___x_1047_, v_x_1031_);
lean_dec_ref(v_ks_1046_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___redArg___boxed(lean_object* v_inst_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
size_t v_x_102__boxed_1053_; uint8_t v_res_1054_; lean_object* v_r_1055_; 
v_x_102__boxed_1053_ = lean_unbox_usize(v_x_1051_);
lean_dec(v_x_1051_);
v_res_1054_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1049_, v_x_1050_, v_x_102__boxed_1053_, v_x_1052_);
v_r_1055_ = lean_box(v_res_1054_);
return v_r_1055_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux(lean_object* v_00_u03b1_1056_, lean_object* v_00_u03b2_1057_, lean_object* v_inst_1058_, lean_object* v_x_1059_, size_t v_x_1060_, lean_object* v_x_1061_){
_start:
{
uint8_t v___x_1062_; 
v___x_1062_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1058_, v_x_1059_, v_x_1060_, v_x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___boxed(lean_object* v_00_u03b1_1063_, lean_object* v_00_u03b2_1064_, lean_object* v_inst_1065_, lean_object* v_x_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_){
_start:
{
size_t v_x_148__boxed_1069_; uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_x_148__boxed_1069_ = lean_unbox_usize(v_x_1067_);
lean_dec(v_x_1067_);
v_res_1070_ = l_Lean_PersistentHashMap_containsAux(v_00_u03b1_1063_, v_00_u03b2_1064_, v_inst_1065_, v_x_1066_, v_x_148__boxed_1069_, v_x_1068_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
lean_object* v___x_1076_; uint64_t v___x_1077_; size_t v___x_1078_; uint8_t v___x_1079_; 
lean_inc(v_x_1075_);
v___x_1076_ = lean_apply_1(v_inst_1073_, v_x_1075_);
v___x_1077_ = lean_unbox_uint64(v___x_1076_);
lean_dec_ref(v___x_1076_);
v___x_1078_ = lean_uint64_to_usize(v___x_1077_);
v___x_1079_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1072_, v_x_1074_, v___x_1078_, v_x_1075_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___redArg___boxed(lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
uint8_t v_res_1084_; lean_object* v_r_1085_; 
v_res_1084_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1080_, v_inst_1081_, v_x_1082_, v_x_1083_);
v_r_1085_ = lean_box(v_res_1084_);
return v_r_1085_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
uint8_t v___x_1092_; 
v___x_1092_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1088_, v_inst_1089_, v_x_1090_, v_x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___boxed(lean_object* v_00_u03b1_1093_, lean_object* v_00_u03b2_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
uint8_t v_res_1099_; lean_object* v_r_1100_; 
v_res_1099_ = l_Lean_PersistentHashMap_contains(v_00_u03b1_1093_, v_00_u03b2_1094_, v_inst_1095_, v_inst_1096_, v_x_1097_, v_x_1098_);
v_r_1100_ = lean_box(v_res_1099_);
return v_r_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg(lean_object* v_a_1101_, lean_object* v_i_1102_, lean_object* v_acc_1103_){
_start:
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = lean_array_get_size(v_a_1101_);
v___x_1105_ = lean_nat_dec_lt(v_i_1102_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_dec(v_i_1102_);
return v_acc_1103_;
}
else
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_array_fget(v_a_1101_, v_i_1102_);
switch(lean_obj_tag(v___x_1106_))
{
case 0:
{
if (lean_obj_tag(v_acc_1103_) == 0)
{
lean_object* v_key_1107_; lean_object* v_val_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1119_; 
v_key_1107_ = lean_ctor_get(v___x_1106_, 0);
v_val_1108_ = lean_ctor_get(v___x_1106_, 1);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1110_ = v___x_1106_;
v_isShared_1111_ = v_isSharedCheck_1119_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_val_1108_);
lean_inc(v_key_1107_);
lean_dec(v___x_1106_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1119_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1112_ = lean_unsigned_to_nat(1u);
v___x_1113_ = lean_nat_add(v_i_1102_, v___x_1112_);
lean_dec(v_i_1102_);
if (v_isShared_1111_ == 0)
{
v___x_1115_ = v___x_1110_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_key_1107_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_val_1108_);
v___x_1115_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
v_i_1102_ = v___x_1113_;
v_acc_1103_ = v___x_1116_;
goto _start;
}
}
}
else
{
lean_object* v___x_1120_; 
lean_dec_ref_known(v_acc_1103_, 1);
lean_dec_ref_known(v___x_1106_, 2);
lean_dec(v_i_1102_);
v___x_1120_ = lean_box(0);
return v___x_1120_;
}
}
case 1:
{
lean_object* v___x_1121_; 
lean_dec_ref_known(v___x_1106_, 1);
lean_dec(v_acc_1103_);
lean_dec(v_i_1102_);
v___x_1121_ = lean_box(0);
return v___x_1121_;
}
default: 
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_add(v_i_1102_, v___x_1122_);
lean_dec(v_i_1102_);
v_i_1102_ = v___x_1123_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg___boxed(lean_object* v_a_1125_, lean_object* v_i_1126_, lean_object* v_acc_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1125_, v_i_1126_, v_acc_1127_);
lean_dec_ref(v_a_1125_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_a_1131_, lean_object* v_i_1132_, lean_object* v_acc_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1131_, v_i_1132_, v_acc_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___boxed(lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_a_1137_, lean_object* v_i_1138_, lean_object* v_acc_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_PersistentHashMap_isUnaryEntries(v_00_u03b1_1135_, v_00_u03b2_1136_, v_a_1137_, v_i_1138_, v_acc_1139_);
lean_dec_ref(v_a_1137_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object* v_x_1141_){
_start:
{
if (lean_obj_tag(v_x_1141_) == 0)
{
lean_object* v_es_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_es_1142_ = lean_ctor_get(v_x_1141_, 0);
lean_inc_ref(v_es_1142_);
lean_dec_ref_known(v_x_1141_, 1);
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_box(0);
v___x_1145_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_es_1142_, v___x_1143_, v___x_1144_);
lean_dec_ref(v_es_1142_);
return v___x_1145_;
}
else
{
lean_object* v_ks_1146_; lean_object* v_vs_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1162_; 
v_ks_1146_ = lean_ctor_get(v_x_1141_, 0);
v_vs_1147_ = lean_ctor_get(v_x_1141_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_x_1141_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1149_ = v_x_1141_;
v_isShared_1150_ = v_isSharedCheck_1162_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_vs_1147_);
lean_inc(v_ks_1146_);
lean_dec(v_x_1141_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1162_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_array_get_size(v_ks_1146_);
v___x_1153_ = lean_nat_dec_eq(v___x_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
lean_del_object(v___x_1149_);
lean_dec_ref(v_vs_1147_);
lean_dec_ref(v_ks_1146_);
v___x_1154_ = lean_box(0);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_array_fget(v_ks_1146_, v___x_1155_);
lean_dec_ref(v_ks_1146_);
v___x_1157_ = lean_array_fget(v_vs_1147_, v___x_1155_);
lean_dec_ref(v_vs_1147_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 0);
lean_ctor_set(v___x_1149_, 1, v___x_1157_);
lean_ctor_set(v___x_1149_, 0, v___x_1156_);
v___x_1159_ = v___x_1149_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
return v___x_1160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode(lean_object* v_00_u03b1_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_x_1165_){
_start:
{
lean_object* v___x_1166_; 
v___x_1166_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg(lean_object* v_inst_1167_, lean_object* v_x_1168_, size_t v_x_1169_, lean_object* v_x_1170_){
_start:
{
if (lean_obj_tag(v_x_1168_) == 0)
{
lean_object* v_es_1171_; lean_object* v___x_1172_; size_t v___x_1173_; size_t v___x_1174_; lean_object* v_j_1175_; lean_object* v_entry_1176_; 
v_es_1171_ = lean_ctor_get(v_x_1168_, 0);
v___x_1172_ = lean_box(2);
v___x_1173_ = ((size_t)31ULL);
v___x_1174_ = lean_usize_land(v_x_1169_, v___x_1173_);
v_j_1175_ = lean_usize_to_nat(v___x_1174_);
v_entry_1176_ = lean_array_get(v___x_1172_, v_es_1171_, v_j_1175_);
switch(lean_obj_tag(v_entry_1176_))
{
case 0:
{
lean_object* v_key_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_key_1177_ = lean_ctor_get(v_entry_1176_, 0);
lean_inc(v_key_1177_);
lean_dec_ref_known(v_entry_1176_, 2);
v___x_1178_ = lean_apply_2(v_inst_1167_, v_x_1170_, v_key_1177_);
v___x_1179_ = lean_unbox(v___x_1178_);
if (v___x_1179_ == 0)
{
lean_dec(v_j_1175_);
return v_x_1168_;
}
else
{
lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1187_; 
lean_inc_ref(v_es_1171_);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_x_1168_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v_x_1168_, 0);
lean_dec(v_unused_1188_);
v___x_1181_ = v_x_1168_;
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
else
{
lean_dec(v_x_1168_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1187_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_array_set(v_es_1171_, v_j_1175_, v___x_1172_);
lean_dec(v_j_1175_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 0, v___x_1183_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1183_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
case 1:
{
lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1223_; 
lean_inc_ref(v_es_1171_);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_x_1168_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v_x_1168_, 0);
lean_dec(v_unused_1224_);
v___x_1190_ = v_x_1168_;
v_isShared_1191_ = v_isSharedCheck_1223_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v_x_1168_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1223_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_node_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1222_; 
v_node_1192_ = lean_ctor_get(v_entry_1176_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v_entry_1176_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1194_ = v_entry_1176_;
v_isShared_1195_ = v_isSharedCheck_1222_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_node_1192_);
lean_dec(v_entry_1176_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1222_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
size_t v___x_1196_; lean_object* v_entries_1197_; size_t v___x_1198_; lean_object* v_newNode_1199_; lean_object* v___x_1200_; 
v___x_1196_ = ((size_t)5ULL);
v_entries_1197_ = lean_array_set(v_es_1171_, v_j_1175_, v___x_1172_);
v___x_1198_ = lean_usize_shift_right(v_x_1169_, v___x_1196_);
v_newNode_1199_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1167_, v_node_1192_, v___x_1198_, v_x_1170_);
lean_inc_ref(v_newNode_1199_);
v___x_1200_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1199_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v___x_1202_; 
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v_newNode_1199_);
v___x_1202_ = v___x_1194_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_newNode_1199_);
v___x_1202_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_array_set(v_entries_1197_, v_j_1175_, v___x_1202_);
lean_dec(v_j_1175_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1203_);
v___x_1205_ = v___x_1190_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
else
{
lean_object* v_val_1208_; lean_object* v_fst_1209_; lean_object* v_snd_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v_newNode_1199_);
lean_del_object(v___x_1194_);
v_val_1208_ = lean_ctor_get(v___x_1200_, 0);
lean_inc(v_val_1208_);
lean_dec_ref_known(v___x_1200_, 1);
v_fst_1209_ = lean_ctor_get(v_val_1208_, 0);
v_snd_1210_ = lean_ctor_get(v_val_1208_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_val_1208_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1212_ = v_val_1208_;
v_isShared_1213_ = v_isSharedCheck_1221_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_snd_1210_);
lean_inc(v_fst_1209_);
lean_dec(v_val_1208_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1221_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_fst_1209_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_snd_1210_);
v___x_1215_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
v___x_1216_ = lean_array_set(v_entries_1197_, v_j_1175_, v___x_1215_);
lean_dec(v_j_1175_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1216_);
v___x_1218_ = v___x_1190_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1175_);
lean_dec(v_x_1170_);
lean_dec_ref(v_inst_1167_);
return v_x_1168_;
}
}
}
else
{
lean_object* v_ks_1225_; lean_object* v_vs_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1240_; 
v_ks_1225_ = lean_ctor_get(v_x_1168_, 0);
v_vs_1226_ = lean_ctor_get(v_x_1168_, 1);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_x_1168_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1228_ = v_x_1168_;
v_isShared_1229_ = v_isSharedCheck_1240_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_vs_1226_);
lean_inc(v_ks_1225_);
lean_dec(v_x_1168_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1240_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1230_; 
v___x_1230_ = l_Array_finIdxOf_x3f___redArg(v_inst_1167_, v_ks_1225_, v_x_1170_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v___x_1232_; 
if (v_isShared_1229_ == 0)
{
v___x_1232_ = v___x_1228_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_ks_1225_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_vs_1226_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
else
{
lean_object* v_val_1234_; lean_object* v_keys_x27_1235_; lean_object* v_vals_x27_1236_; lean_object* v___x_1238_; 
v_val_1234_ = lean_ctor_get(v___x_1230_, 0);
lean_inc_n(v_val_1234_, 2);
lean_dec_ref_known(v___x_1230_, 1);
v_keys_x27_1235_ = l_Array_eraseIdx___redArg(v_ks_1225_, v_val_1234_);
v_vals_x27_1236_ = l_Array_eraseIdx___redArg(v_vs_1226_, v_val_1234_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v_vals_x27_1236_);
lean_ctor_set(v___x_1228_, 0, v_keys_x27_1235_);
v___x_1238_ = v___x_1228_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_keys_x27_1235_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_vals_x27_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg___boxed(lean_object* v_inst_1241_, lean_object* v_x_1242_, lean_object* v_x_1243_, lean_object* v_x_1244_){
_start:
{
size_t v_x_224__boxed_1245_; lean_object* v_res_1246_; 
v_x_224__boxed_1245_ = lean_unbox_usize(v_x_1243_);
lean_dec(v_x_1243_);
v_res_1246_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1241_, v_x_1242_, v_x_224__boxed_1245_, v_x_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux(lean_object* v_00_u03b1_1247_, lean_object* v_00_u03b2_1248_, lean_object* v_inst_1249_, lean_object* v_x_1250_, size_t v_x_1251_, lean_object* v_x_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1249_, v_x_1250_, v_x_1251_, v_x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___boxed(lean_object* v_00_u03b1_1254_, lean_object* v_00_u03b2_1255_, lean_object* v_inst_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
size_t v_x_365__boxed_1260_; lean_object* v_res_1261_; 
v_x_365__boxed_1260_ = lean_unbox_usize(v_x_1258_);
lean_dec(v_x_1258_);
v_res_1261_ = l_Lean_PersistentHashMap_eraseAux(v_00_u03b1_1254_, v_00_u03b2_1255_, v_inst_1256_, v_x_1257_, v_x_365__boxed_1260_, v_x_1259_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object* v_x_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_){
_start:
{
lean_object* v___x_1266_; uint64_t v___x_1267_; size_t v_h_1268_; lean_object* v___x_1269_; 
lean_inc(v_x_1265_);
v___x_1266_ = lean_apply_1(v_x_1263_, v_x_1265_);
v___x_1267_ = lean_unbox_uint64(v___x_1266_);
lean_dec_ref(v___x_1266_);
v_h_1268_ = lean_uint64_to_usize(v___x_1267_);
v___x_1269_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_x_1262_, v_x_1264_, v_h_1268_, v_x_1265_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase(lean_object* v_00_u03b1_1270_, lean_object* v_00_u03b2_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_PersistentHashMap_erase___redArg(v_x_1272_, v_x_1273_, v_x_1274_, v_x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg(lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_f_1279_, lean_object* v_x_1280_, size_t v_x_1281_, size_t v_x_1282_, lean_object* v_x_1283_){
_start:
{
if (lean_obj_tag(v_x_1280_) == 0)
{
lean_object* v_es_1284_; size_t v___x_1285_; size_t v___x_1286_; lean_object* v_j_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_es_1284_ = lean_ctor_get(v_x_1280_, 0);
v___x_1285_ = ((size_t)31ULL);
v___x_1286_ = lean_usize_land(v_x_1281_, v___x_1285_);
v_j_1287_ = lean_usize_to_nat(v___x_1286_);
v___x_1288_ = lean_array_get_size(v_es_1284_);
v___x_1289_ = lean_nat_dec_lt(v_j_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_dec(v_j_1287_);
lean_dec(v_x_1283_);
lean_dec_ref(v_f_1279_);
lean_dec_ref(v_inst_1278_);
lean_dec_ref(v_inst_1277_);
return v_x_1280_;
}
else
{
lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1358_; 
lean_inc_ref(v_es_1284_);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_x_1280_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v_x_1280_, 0);
lean_dec(v_unused_1359_);
v___x_1291_ = v_x_1280_;
v_isShared_1292_ = v_isSharedCheck_1358_;
goto v_resetjp_1290_;
}
else
{
lean_dec(v_x_1280_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1358_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_v_1293_; lean_object* v___x_1294_; lean_object* v_xs_x27_1295_; lean_object* v___y_1297_; 
v_v_1293_ = lean_array_fget(v_es_1284_, v_j_1287_);
v___x_1294_ = lean_box(0);
v_xs_x27_1295_ = lean_array_fset(v_es_1284_, v_j_1287_, v___x_1294_);
switch(lean_obj_tag(v_v_1293_))
{
case 0:
{
lean_object* v_key_1302_; lean_object* v_val_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
lean_dec_ref(v_inst_1278_);
v_key_1302_ = lean_ctor_get(v_v_1293_, 0);
v_val_1303_ = lean_ctor_get(v_v_1293_, 1);
lean_inc(v_key_1302_);
lean_inc(v_x_1283_);
v___x_1304_ = lean_apply_2(v_inst_1277_, v_x_1283_, v_key_1302_);
v___x_1305_ = lean_unbox(v___x_1304_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = lean_apply_1(v_f_1279_, v___x_1306_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_dec(v_x_1283_);
v___y_1297_ = v_v_1293_;
goto v___jp_1296_;
}
else
{
lean_object* v_val_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
lean_inc(v_val_1303_);
lean_inc(v_key_1302_);
lean_dec_ref_known(v_v_1293_, 2);
v_val_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_val_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1302_, v_val_1303_, v_x_1283_, v_val_1308_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
v___y_1297_ = v___x_1314_;
goto v___jp_1296_;
}
}
}
}
else
{
lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1327_; 
lean_inc(v_val_1303_);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_v_1293_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; lean_object* v_unused_1329_; 
v_unused_1328_ = lean_ctor_get(v_v_1293_, 1);
lean_dec(v_unused_1328_);
v_unused_1329_ = lean_ctor_get(v_v_1293_, 0);
lean_dec(v_unused_1329_);
v___x_1318_ = v_v_1293_;
v_isShared_1319_ = v_isSharedCheck_1327_;
goto v_resetjp_1317_;
}
else
{
lean_dec(v_v_1293_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1327_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_val_1303_);
v___x_1321_ = lean_apply_1(v_f_1279_, v___x_1320_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v___x_1322_; 
lean_del_object(v___x_1318_);
lean_dec(v_x_1283_);
v___x_1322_ = lean_box(2);
v___y_1297_ = v___x_1322_;
goto v___jp_1296_;
}
else
{
lean_object* v_val_1323_; lean_object* v___x_1325_; 
v_val_1323_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_val_1323_);
lean_dec_ref_known(v___x_1321_, 1);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 1, v_val_1323_);
lean_ctor_set(v___x_1318_, 0, v_x_1283_);
v___x_1325_ = v___x_1318_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_x_1283_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_val_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
v___y_1297_ = v___x_1325_;
goto v___jp_1296_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1353_; 
v_node_1330_ = lean_ctor_get(v_v_1293_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_v_1293_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1332_ = v_v_1293_;
v_isShared_1333_ = v_isSharedCheck_1353_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_node_1330_);
lean_dec(v_v_1293_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1353_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
size_t v___x_1334_; size_t v___x_1335_; size_t v___x_1336_; size_t v___x_1337_; lean_object* v_newNode_1338_; lean_object* v___x_1339_; 
v___x_1334_ = ((size_t)5ULL);
v___x_1335_ = lean_usize_shift_right(v_x_1281_, v___x_1334_);
v___x_1336_ = ((size_t)1ULL);
v___x_1337_ = lean_usize_add(v_x_1282_, v___x_1336_);
v_newNode_1338_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1277_, v_inst_1278_, v_f_1279_, v_node_1330_, v___x_1335_, v___x_1337_, v_x_1283_);
lean_inc_ref(v_newNode_1338_);
v___x_1339_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1338_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1341_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v_newNode_1338_);
v___x_1341_ = v___x_1332_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_newNode_1338_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
v___y_1297_ = v___x_1341_;
goto v___jp_1296_;
}
}
else
{
lean_object* v_val_1343_; lean_object* v_fst_1344_; lean_object* v_snd_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v_newNode_1338_);
lean_del_object(v___x_1332_);
v_val_1343_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_val_1343_);
lean_dec_ref_known(v___x_1339_, 1);
v_fst_1344_ = lean_ctor_get(v_val_1343_, 0);
v_snd_1345_ = lean_ctor_get(v_val_1343_, 1);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_val_1343_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v_val_1343_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_snd_1345_);
lean_inc(v_fst_1344_);
lean_dec(v_val_1343_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_fst_1344_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_snd_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
v___y_1297_ = v___x_1350_;
goto v___jp_1296_;
}
}
}
}
}
default: 
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec_ref(v_inst_1278_);
lean_dec_ref(v_inst_1277_);
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_apply_1(v_f_1279_, v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_dec(v_x_1283_);
v___y_1297_ = v_v_1293_;
goto v___jp_1296_;
}
else
{
lean_object* v_val_1356_; lean_object* v___x_1357_; 
v_val_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_x_1283_);
lean_ctor_set(v___x_1357_, 1, v_val_1356_);
v___y_1297_ = v___x_1357_;
goto v___jp_1296_;
}
}
}
v___jp_1296_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = lean_array_fset(v_xs_x27_1295_, v_j_1287_, v___y_1297_);
lean_dec(v_j_1287_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1298_);
v___x_1300_ = v___x_1291_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
else
{
lean_object* v_ks_1360_; lean_object* v_vs_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1394_; 
v_ks_1360_ = lean_ctor_get(v_x_1280_, 0);
v_vs_1361_ = lean_ctor_get(v_x_1280_, 1);
v_isSharedCheck_1394_ = !lean_is_exclusive(v_x_1280_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1363_ = v_x_1280_;
v_isShared_1364_ = v_isSharedCheck_1394_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_vs_1361_);
lean_inc(v_ks_1360_);
lean_dec(v_x_1280_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1394_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; 
lean_inc(v_x_1283_);
lean_inc_ref(v_inst_1277_);
v___x_1365_ = l_Array_finIdxOf_x3f___redArg(v_inst_1277_, v_ks_1360_, v_x_1283_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1367_; 
if (v_isShared_1364_ == 0)
{
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_ks_1360_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_vs_1361_);
v___x_1367_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_apply_1(v_f_1279_, v___x_1368_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_dec(v_x_1283_);
lean_dec_ref(v_inst_1278_);
lean_dec_ref(v_inst_1277_);
return v___x_1367_;
}
else
{
lean_object* v_val_1370_; lean_object* v___x_1371_; 
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_1277_, v_inst_1278_, v___x_1367_, v_x_1281_, v_x_1282_, v_x_1283_, v_val_1370_);
return v___x_1371_;
}
}
}
else
{
lean_object* v_val_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1393_; 
lean_dec_ref(v_inst_1278_);
lean_dec_ref(v_inst_1277_);
v_val_1373_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1375_ = v___x_1365_;
v_isShared_1376_ = v_isSharedCheck_1393_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_val_1373_);
lean_dec(v___x_1365_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1393_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v_v_x27_1377_; lean_object* v_keys_1378_; lean_object* v_vals_1379_; lean_object* v___x_1381_; 
v_v_x27_1377_ = lean_array_fget(v_vs_1361_, v_val_1373_);
lean_inc(v_val_1373_);
v_keys_1378_ = l_Array_eraseIdx___redArg(v_ks_1360_, v_val_1373_);
v_vals_1379_ = l_Array_eraseIdx___redArg(v_vs_1361_, v_val_1373_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v_v_x27_1377_);
v___x_1381_ = v___x_1375_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_v_x27_1377_);
v___x_1381_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_apply_1(v_f_1279_, v___x_1381_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v___x_1384_; 
lean_dec(v_x_1283_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v_vals_1379_);
lean_ctor_set(v___x_1363_, 0, v_keys_1378_);
v___x_1384_ = v___x_1363_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_keys_1378_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_vals_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
else
{
lean_object* v_val_1386_; lean_object* v_keys_1387_; lean_object* v_vals_1388_; lean_object* v___x_1390_; 
v_val_1386_ = lean_ctor_get(v___x_1382_, 0);
lean_inc(v_val_1386_);
lean_dec_ref_known(v___x_1382_, 1);
v_keys_1387_ = lean_array_push(v_keys_1378_, v_x_1283_);
v_vals_1388_ = lean_array_push(v_vals_1379_, v_val_1386_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 1, v_vals_1388_);
lean_ctor_set(v___x_1363_, 0, v_keys_1387_);
v___x_1390_ = v___x_1363_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_keys_1387_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_vals_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg___boxed(lean_object* v_inst_1395_, lean_object* v_inst_1396_, lean_object* v_f_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_){
_start:
{
size_t v_x_458__boxed_1402_; size_t v_x_459__boxed_1403_; lean_object* v_res_1404_; 
v_x_458__boxed_1402_ = lean_unbox_usize(v_x_1399_);
lean_dec(v_x_1399_);
v_x_459__boxed_1403_ = lean_unbox_usize(v_x_1400_);
lean_dec(v_x_1400_);
v_res_1404_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1395_, v_inst_1396_, v_f_1397_, v_x_1398_, v_x_458__boxed_1402_, v_x_459__boxed_1403_, v_x_1401_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux(lean_object* v_00_u03b1_1405_, lean_object* v_00_u03b2_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_f_1409_, lean_object* v_x_1410_, size_t v_x_1411_, size_t v_x_1412_, lean_object* v_x_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1407_, v_inst_1408_, v_f_1409_, v_x_1410_, v_x_1411_, v_x_1412_, v_x_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_f_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
size_t v_x_680__boxed_1424_; size_t v_x_681__boxed_1425_; lean_object* v_res_1426_; 
v_x_680__boxed_1424_ = lean_unbox_usize(v_x_1421_);
lean_dec(v_x_1421_);
v_x_681__boxed_1425_ = lean_unbox_usize(v_x_1422_);
lean_dec(v_x_1422_);
v_res_1426_ = l_Lean_PersistentHashMap_alterAux(v_00_u03b1_1415_, v_00_u03b2_1416_, v_inst_1417_, v_inst_1418_, v_f_1419_, v_x_1420_, v_x_680__boxed_1424_, v_x_681__boxed_1425_, v_x_1423_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter___redArg(lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v_x_1431_){
_start:
{
lean_object* v___x_1432_; uint64_t v___x_1433_; size_t v_h_1434_; size_t v___x_1435_; lean_object* v___x_1436_; 
lean_inc_ref(v_x_1428_);
lean_inc(v_x_1430_);
v___x_1432_ = lean_apply_1(v_x_1428_, v_x_1430_);
v___x_1433_ = lean_unbox_uint64(v___x_1432_);
lean_dec_ref(v___x_1432_);
v_h_1434_ = lean_uint64_to_usize(v___x_1433_);
v___x_1435_ = ((size_t)1ULL);
v___x_1436_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1427_, v_x_1428_, v_x_1431_, v_x_1429_, v_h_1434_, v___x_1435_, v_x_1430_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter(lean_object* v_00_u03b1_1437_, lean_object* v_00_u03b2_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_){
_start:
{
lean_object* v___x_1444_; uint64_t v___x_1445_; size_t v_h_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
lean_inc_ref(v_x_1440_);
lean_inc(v_x_1442_);
v___x_1444_ = lean_apply_1(v_x_1440_, v_x_1442_);
v___x_1445_ = lean_unbox_uint64(v___x_1444_);
lean_dec_ref(v___x_1444_);
v_h_1446_ = lean_uint64_to_usize(v___x_1445_);
v___x_1447_ = ((size_t)1ULL);
v___x_1448_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1439_, v_x_1440_, v_x_1443_, v_x_1441_, v_h_1446_, v___x_1447_, v_x_1442_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed(lean_object* v_i_1449_, lean_object* v_inst_1450_, lean_object* v_f_1451_, lean_object* v_keys_1452_, lean_object* v_vals_1453_, lean_object* v_____do__lift_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(v_i_1449_, v_inst_1450_, v_f_1451_, v_keys_1452_, v_vals_1453_, v_____do__lift_1454_);
lean_dec(v_i_1449_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(lean_object* v_inst_1456_, lean_object* v_f_1457_, lean_object* v_keys_1458_, lean_object* v_vals_1459_, lean_object* v_i_1460_, lean_object* v_acc_1461_){
_start:
{
lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = lean_array_get_size(v_keys_1458_);
v___x_1463_ = lean_nat_dec_lt(v_i_1460_, v___x_1462_);
if (v___x_1463_ == 0)
{
lean_object* v_toApplicative_1464_; lean_object* v_toPure_1465_; lean_object* v___x_1466_; 
lean_dec(v_i_1460_);
lean_dec_ref(v_vals_1459_);
lean_dec_ref(v_keys_1458_);
lean_dec(v_f_1457_);
v_toApplicative_1464_ = lean_ctor_get(v_inst_1456_, 0);
lean_inc_ref(v_toApplicative_1464_);
lean_dec_ref(v_inst_1456_);
v_toPure_1465_ = lean_ctor_get(v_toApplicative_1464_, 1);
lean_inc(v_toPure_1465_);
lean_dec_ref(v_toApplicative_1464_);
v___x_1466_ = lean_apply_2(v_toPure_1465_, lean_box(0), v_acc_1461_);
return v___x_1466_;
}
else
{
lean_object* v_toBind_1467_; lean_object* v___f_1468_; lean_object* v_k_1469_; lean_object* v_v_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_toBind_1467_ = lean_ctor_get(v_inst_1456_, 1);
lean_inc(v_toBind_1467_);
lean_inc_ref(v_vals_1459_);
lean_inc_ref(v_keys_1458_);
lean_inc(v_f_1457_);
lean_inc(v_i_1460_);
v___f_1468_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1468_, 0, v_i_1460_);
lean_closure_set(v___f_1468_, 1, v_inst_1456_);
lean_closure_set(v___f_1468_, 2, v_f_1457_);
lean_closure_set(v___f_1468_, 3, v_keys_1458_);
lean_closure_set(v___f_1468_, 4, v_vals_1459_);
v_k_1469_ = lean_array_fget(v_keys_1458_, v_i_1460_);
lean_dec_ref(v_keys_1458_);
v_v_1470_ = lean_array_fget(v_vals_1459_, v_i_1460_);
lean_dec(v_i_1460_);
lean_dec_ref(v_vals_1459_);
v___x_1471_ = lean_apply_3(v_f_1457_, v_acc_1461_, v_k_1469_, v_v_1470_);
v___x_1472_ = lean_apply_4(v_toBind_1467_, lean_box(0), lean_box(0), v___x_1471_, v___f_1468_);
return v___x_1472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(lean_object* v_i_1473_, lean_object* v_inst_1474_, lean_object* v_f_1475_, lean_object* v_keys_1476_, lean_object* v_vals_1477_, lean_object* v_____do__lift_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1479_ = lean_unsigned_to_nat(1u);
v___x_1480_ = lean_nat_add(v_i_1473_, v___x_1479_);
v___x_1481_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1474_, v_f_1475_, v_keys_1476_, v_vals_1477_, v___x_1480_, v_____do__lift_1478_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse(lean_object* v_m_1482_, lean_object* v_inst_1483_, lean_object* v_00_u03c3_1484_, lean_object* v_00_u03b1_1485_, lean_object* v_00_u03b2_1486_, lean_object* v_f_1487_, lean_object* v_keys_1488_, lean_object* v_vals_1489_, lean_object* v_heq_1490_, lean_object* v_i_1491_, lean_object* v_acc_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1483_, v_f_1487_, v_keys_1488_, v_vals_1489_, v_i_1491_, v_acc_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object* v_inst_1494_, lean_object* v_f_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_){
_start:
{
if (lean_obj_tag(v_x_1496_) == 0)
{
lean_object* v_toApplicative_1498_; lean_object* v_toPure_1499_; lean_object* v_es_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v_toApplicative_1498_ = lean_ctor_get(v_inst_1494_, 0);
v_toPure_1499_ = lean_ctor_get(v_toApplicative_1498_, 1);
v_es_1500_ = lean_ctor_get(v_x_1496_, 0);
lean_inc_ref(v_es_1500_);
lean_dec_ref_known(v_x_1496_, 1);
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = lean_array_get_size(v_es_1500_);
v___x_1503_ = lean_nat_dec_lt(v___x_1501_, v___x_1502_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
lean_inc(v_toPure_1499_);
lean_dec_ref(v_es_1500_);
lean_dec(v_f_1495_);
lean_dec_ref(v_inst_1494_);
v___x_1504_ = lean_apply_2(v_toPure_1499_, lean_box(0), v_x_1497_);
return v___x_1504_;
}
else
{
lean_object* v___f_1505_; uint8_t v___x_1506_; 
lean_inc(v_toPure_1499_);
lean_inc_ref(v_inst_1494_);
v___f_1505_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1505_, 0, v_f_1495_);
lean_closure_set(v___f_1505_, 1, v_inst_1494_);
lean_closure_set(v___f_1505_, 2, v_toPure_1499_);
v___x_1506_ = lean_nat_dec_le(v___x_1502_, v___x_1502_);
if (v___x_1506_ == 0)
{
if (v___x_1503_ == 0)
{
lean_object* v___x_1507_; 
lean_inc(v_toPure_1499_);
lean_dec_ref(v___f_1505_);
lean_dec_ref(v_es_1500_);
lean_dec_ref(v_inst_1494_);
v___x_1507_ = lean_apply_2(v_toPure_1499_, lean_box(0), v_x_1497_);
return v___x_1507_;
}
else
{
size_t v___x_1508_; size_t v___x_1509_; lean_object* v___x_1510_; 
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = lean_usize_of_nat(v___x_1502_);
v___x_1510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1494_, v___f_1505_, v_es_1500_, v___x_1508_, v___x_1509_, v_x_1497_);
return v___x_1510_;
}
}
else
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = ((size_t)0ULL);
v___x_1512_ = lean_usize_of_nat(v___x_1502_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1494_, v___f_1505_, v_es_1500_, v___x_1511_, v___x_1512_, v_x_1497_);
return v___x_1513_;
}
}
}
else
{
lean_object* v_ks_1514_; lean_object* v_vs_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v_ks_1514_ = lean_ctor_get(v_x_1496_, 0);
lean_inc_ref(v_ks_1514_);
v_vs_1515_ = lean_ctor_get(v_x_1496_, 1);
lean_inc_ref(v_vs_1515_);
lean_dec_ref_known(v_x_1496_, 2);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1494_, v_f_1495_, v_ks_1514_, v_vs_1515_, v___x_1516_, v_x_1497_);
return v___x_1517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0(lean_object* v_f_1518_, lean_object* v_inst_1519_, lean_object* v_toPure_1520_, lean_object* v_acc_1521_, lean_object* v_entry_1522_){
_start:
{
switch(lean_obj_tag(v_entry_1522_))
{
case 0:
{
lean_object* v_key_1523_; lean_object* v_val_1524_; lean_object* v___x_1525_; 
lean_dec(v_toPure_1520_);
lean_dec_ref(v_inst_1519_);
v_key_1523_ = lean_ctor_get(v_entry_1522_, 0);
lean_inc(v_key_1523_);
v_val_1524_ = lean_ctor_get(v_entry_1522_, 1);
lean_inc(v_val_1524_);
lean_dec_ref_known(v_entry_1522_, 2);
v___x_1525_ = lean_apply_3(v_f_1518_, v_acc_1521_, v_key_1523_, v_val_1524_);
return v___x_1525_;
}
case 1:
{
lean_object* v_node_1526_; lean_object* v___x_1527_; 
lean_dec(v_toPure_1520_);
v_node_1526_ = lean_ctor_get(v_entry_1522_, 0);
lean_inc(v_node_1526_);
lean_dec_ref_known(v_entry_1522_, 1);
v___x_1527_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1519_, v_f_1518_, v_node_1526_, v_acc_1521_);
return v___x_1527_;
}
default: 
{
lean_object* v___x_1528_; 
lean_dec_ref(v_inst_1519_);
lean_dec(v_f_1518_);
v___x_1528_ = lean_apply_2(v_toPure_1520_, lean_box(0), v_acc_1521_);
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux(lean_object* v_m_1529_, lean_object* v_inst_1530_, lean_object* v_00_u03c3_1531_, lean_object* v_00_u03b1_1532_, lean_object* v_00_u03b2_1533_, lean_object* v_f_1534_, lean_object* v_x_1535_, lean_object* v_x_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1530_, v_f_1534_, v_x_1535_, v_x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___redArg(lean_object* v_inst_1538_, lean_object* v_map_1539_, lean_object* v_f_1540_, lean_object* v_init_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1538_, v_f_1540_, v_map_1539_, v_init_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM(lean_object* v_m_1543_, lean_object* v_inst_1544_, lean_object* v_00_u03c3_1545_, lean_object* v_00_u03b1_1546_, lean_object* v_00_u03b2_1547_, lean_object* v_x_1548_, lean_object* v_x_1549_, lean_object* v_map_1550_, lean_object* v_f_1551_, lean_object* v_init_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1544_, v_f_1551_, v_map_1550_, v_init_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___boxed(lean_object* v_m_1554_, lean_object* v_inst_1555_, lean_object* v_00_u03c3_1556_, lean_object* v_00_u03b1_1557_, lean_object* v_00_u03b2_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_, lean_object* v_map_1561_, lean_object* v_f_1562_, lean_object* v_init_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_PersistentHashMap_foldlM(v_m_1554_, v_inst_1555_, v_00_u03c3_1556_, v_00_u03b1_1557_, v_00_u03b2_1558_, v_x_1559_, v_x_1560_, v_map_1561_, v_f_1562_, v_init_1563_);
lean_dec_ref(v_x_1560_);
lean_dec_ref(v_x_1559_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg___lam__0(lean_object* v_f_1565_, lean_object* v_x_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_apply_2(v_f_1565_, v___y_1567_, v___y_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg(lean_object* v_inst_1570_, lean_object* v_map_1571_, lean_object* v_f_1572_){
_start:
{
lean_object* v___f_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___f_1573_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1573_, 0, v_f_1572_);
v___x_1574_ = lean_box(0);
v___x_1575_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1570_, v___f_1573_, v_map_1571_, v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM(lean_object* v_m_1576_, lean_object* v_inst_1577_, lean_object* v_00_u03b1_1578_, lean_object* v_00_u03b2_1579_, lean_object* v_x_1580_, lean_object* v_x_1581_, lean_object* v_map_1582_, lean_object* v_f_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_1577_, v_map_1582_, v_f_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___boxed(lean_object* v_m_1585_, lean_object* v_inst_1586_, lean_object* v_00_u03b1_1587_, lean_object* v_00_u03b2_1588_, lean_object* v_x_1589_, lean_object* v_x_1590_, lean_object* v_map_1591_, lean_object* v_f_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_PersistentHashMap_forM(v_m_1585_, v_inst_1586_, v_00_u03b1_1587_, v_00_u03b2_1588_, v_x_1589_, v_x_1590_, v_map_1591_, v_f_1592_);
lean_dec_ref(v_x_1590_);
lean_dec_ref(v_x_1589_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg___lam__0(lean_object* v_f_1594_, lean_object* v_x1_1595_, lean_object* v_x2_1596_, lean_object* v_x3_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_apply_3(v_f_1594_, v_x1_1595_, v_x2_1596_, v_x3_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object* v_map_1618_, lean_object* v_f_1619_, lean_object* v_init_1620_){
_start:
{
lean_object* v___f_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___f_1621_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1621_, 0, v_f_1619_);
v___x_1622_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1623_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1622_, v___f_1621_, v_map_1618_, v_init_1620_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl(lean_object* v_00_u03c3_1624_, lean_object* v_00_u03b1_1625_, lean_object* v_00_u03b2_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_map_1629_, lean_object* v_f_1630_, lean_object* v_init_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_1629_, v_f_1630_, v_init_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___boxed(lean_object* v_00_u03c3_1633_, lean_object* v_00_u03b1_1634_, lean_object* v_00_u03b2_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_, lean_object* v_map_1638_, lean_object* v_f_1639_, lean_object* v_init_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_PersistentHashMap_foldl(v_00_u03c3_1633_, v_00_u03b1_1634_, v_00_u03b2_1635_, v_x_1636_, v_x_1637_, v_map_1638_, v_f_1639_, v_init_1640_);
lean_dec_ref(v_x_1637_);
lean_dec_ref(v_x_1636_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__0(lean_object* v_x_1642_){
_start:
{
if (lean_obj_tag(v_x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v_x_1642_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_x_1642_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v_x_1642_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v_x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v_x_1642_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_x_1642_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v_x_1642_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v_x_1642_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__1(lean_object* v_toPure_1659_, lean_object* v_result_1660_){
_start:
{
lean_object* v_a_1661_; lean_object* v___x_1662_; 
v_a_1661_ = lean_ctor_get(v_result_1660_, 0);
lean_inc(v_a_1661_);
lean_dec_ref(v_result_1660_);
v___x_1662_ = lean_apply_2(v_toPure_1659_, lean_box(0), v_a_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__2(lean_object* v_toFunctor_1663_, lean_object* v_f_1664_, lean_object* v_intoError_1665_, lean_object* v_s_1666_, lean_object* v_a_1667_, lean_object* v_b_1668_){
_start:
{
lean_object* v_map_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1678_; 
v_map_1669_ = lean_ctor_get(v_toFunctor_1663_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_toFunctor_1663_);
if (v_isSharedCheck_1678_ == 0)
{
lean_object* v_unused_1679_; 
v_unused_1679_ = lean_ctor_get(v_toFunctor_1663_, 1);
lean_dec(v_unused_1679_);
v___x_1671_ = v_toFunctor_1663_;
v_isShared_1672_ = v_isSharedCheck_1678_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_map_1669_);
lean_dec(v_toFunctor_1663_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1678_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v_b_1668_);
lean_ctor_set(v___x_1671_, 0, v_a_1667_);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1667_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_b_1668_);
v___x_1674_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_apply_2(v_f_1664_, v___x_1674_, v_s_1666_);
v___x_1676_ = lean_apply_4(v_map_1669_, lean_box(0), lean_box(0), v_intoError_1665_, v___x_1675_);
return v___x_1676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg(lean_object* v_inst_1681_, lean_object* v_map_1682_, lean_object* v_init_1683_, lean_object* v_f_1684_){
_start:
{
lean_object* v_toApplicative_1685_; lean_object* v_toBind_1686_; lean_object* v___f_1687_; lean_object* v___f_1688_; lean_object* v___f_1689_; lean_object* v___f_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v_toFunctor_1697_; lean_object* v_toPure_1698_; lean_object* v_intoError_1699_; lean_object* v___f_1700_; lean_object* v___f_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v_toApplicative_1685_ = lean_ctor_get(v_inst_1681_, 0);
lean_inc_ref(v_toApplicative_1685_);
v_toBind_1686_ = lean_ctor_get(v_inst_1681_, 1);
lean_inc(v_toBind_1686_);
lean_inc_ref_n(v_inst_1681_, 6);
v___f_1687_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1687_, 0, v_inst_1681_);
v___f_1688_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1688_, 0, v_inst_1681_);
v___f_1689_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1689_, 0, v_inst_1681_);
v___f_1690_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1690_, 0, v_inst_1681_);
v___x_1691_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1691_, 0, lean_box(0));
lean_closure_set(v___x_1691_, 1, lean_box(0));
lean_closure_set(v___x_1691_, 2, v_inst_1681_);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v___f_1687_);
v___x_1693_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1693_, 0, lean_box(0));
lean_closure_set(v___x_1693_, 1, lean_box(0));
lean_closure_set(v___x_1693_, 2, v_inst_1681_);
v___x_1694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
lean_ctor_set(v___x_1694_, 2, v___f_1688_);
lean_ctor_set(v___x_1694_, 3, v___f_1689_);
lean_ctor_set(v___x_1694_, 4, v___f_1690_);
v___x_1695_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1695_, 0, lean_box(0));
lean_closure_set(v___x_1695_, 1, lean_box(0));
lean_closure_set(v___x_1695_, 2, v_inst_1681_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v_toFunctor_1697_ = lean_ctor_get(v_toApplicative_1685_, 0);
lean_inc_ref(v_toFunctor_1697_);
v_toPure_1698_ = lean_ctor_get(v_toApplicative_1685_, 1);
lean_inc(v_toPure_1698_);
lean_dec_ref(v_toApplicative_1685_);
v_intoError_1699_ = ((lean_object*)(l_Lean_PersistentHashMap_forIn___redArg___closed__0));
v___f_1700_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1700_, 0, v_toPure_1698_);
v___f_1701_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__2), 6, 3);
lean_closure_set(v___f_1701_, 0, v_toFunctor_1697_);
lean_closure_set(v___f_1701_, 1, v_f_1684_);
lean_closure_set(v___f_1701_, 2, v_intoError_1699_);
lean_inc_ref(v_map_1682_);
v___x_1702_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1696_, v___f_1701_, v_map_1682_, v_init_1683_);
v___x_1703_ = lean_apply_4(v_toBind_1686_, lean_box(0), lean_box(0), v___x_1702_, v___f_1700_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___boxed(lean_object* v_inst_1704_, lean_object* v_map_1705_, lean_object* v_init_1706_, lean_object* v_f_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1704_, v_map_1705_, v_init_1706_, v_f_1707_);
lean_dec_ref(v_map_1705_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn(lean_object* v_m_1709_, lean_object* v_00_u03c3_1710_, lean_object* v_00_u03b1_1711_, lean_object* v_00_u03b2_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_, lean_object* v_inst_1715_, lean_object* v_map_1716_, lean_object* v_init_1717_, lean_object* v_f_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1715_, v_map_1716_, v_init_1717_, v_f_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___boxed(lean_object* v_m_1720_, lean_object* v_00_u03c3_1721_, lean_object* v_00_u03b1_1722_, lean_object* v_00_u03b2_1723_, lean_object* v_x_1724_, lean_object* v_x_1725_, lean_object* v_inst_1726_, lean_object* v_map_1727_, lean_object* v_init_1728_, lean_object* v_f_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_PersistentHashMap_forIn(v_m_1720_, v_00_u03c3_1721_, v_00_u03b1_1722_, v_00_u03b2_1723_, v_x_1724_, v_x_1725_, v_inst_1726_, v_map_1727_, v_init_1728_, v_f_1729_);
lean_dec_ref(v_map_1727_);
lean_dec_ref(v_x_1725_);
lean_dec_ref(v_x_1724_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_inst_1731_, lean_object* v_00_u03b2_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1731_, v___y_1733_, v___y_1734_, v___y_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed(lean_object* v_inst_1737_, lean_object* v_00_u03b2_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(v_inst_1737_, v_00_u03b2_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
lean_dec_ref(v___y_1739_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1743_){
_start:
{
lean_object* v___f_1744_; 
v___f_1744_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1744_, 0, v_inst_1743_);
return v___f_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad(lean_object* v_m_1745_, lean_object* v_00_u03b1_1746_, lean_object* v_00_u03b2_1747_, lean_object* v_x_1748_, lean_object* v_x_1749_, lean_object* v_inst_1750_){
_start:
{
lean_object* v___f_1751_; 
v___f_1751_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1751_, 0, v_inst_1750_);
return v___f_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___boxed(lean_object* v_m_1752_, lean_object* v_00_u03b1_1753_, lean_object* v_00_u03b2_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_, lean_object* v_inst_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_PersistentHashMap_instForInProdOfMonad(v_m_1752_, v_00_u03b1_1753_, v_00_u03b2_1754_, v_x_1755_, v_x_1756_, v_inst_1757_);
lean_dec_ref(v_x_1756_);
lean_dec_ref(v_x_1755_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__0(lean_object* v_toPure_1759_, lean_object* v_entries_x27_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_entries_x27_1760_);
v___x_1762_ = lean_apply_2(v_toPure_1759_, lean_box(0), v___x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__1(lean_object* v_toPure_1763_, lean_object* v_____do__lift_1764_){
_start:
{
lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1765_, 0, v_____do__lift_1764_);
v___x_1766_ = lean_apply_2(v_toPure_1763_, lean_box(0), v___x_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__2(lean_object* v_key_1767_, lean_object* v_toPure_1768_, lean_object* v_____do__lift_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v_key_1767_);
lean_ctor_set(v___x_1770_, 1, v_____do__lift_1769_);
v___x_1771_ = lean_apply_2(v_toPure_1768_, lean_box(0), v___x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__4(lean_object* v_ks_1772_, lean_object* v_toPure_1773_, lean_object* v_____x_1774_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_ks_1772_);
lean_ctor_set(v___x_1775_, 1, v_____x_1774_);
v___x_1776_ = lean_apply_2(v_toPure_1773_, lean_box(0), v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg(lean_object* v_inst_1777_, lean_object* v_f_1778_, lean_object* v_n_1779_){
_start:
{
if (lean_obj_tag(v_n_1779_) == 0)
{
lean_object* v_toApplicative_1780_; lean_object* v_toBind_1781_; lean_object* v_toPure_1782_; lean_object* v_es_1783_; lean_object* v___f_1784_; lean_object* v___f_1785_; lean_object* v___f_1786_; size_t v_sz_1787_; size_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_toApplicative_1780_ = lean_ctor_get(v_inst_1777_, 0);
v_toBind_1781_ = lean_ctor_get(v_inst_1777_, 1);
lean_inc_n(v_toBind_1781_, 2);
v_toPure_1782_ = lean_ctor_get(v_toApplicative_1780_, 1);
v_es_1783_ = lean_ctor_get(v_n_1779_, 0);
lean_inc_ref(v_es_1783_);
lean_dec_ref_known(v_n_1779_, 1);
lean_inc_n(v_toPure_1782_, 3);
v___f_1784_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1784_, 0, v_toPure_1782_);
v___f_1785_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1785_, 0, v_toPure_1782_);
lean_inc_ref(v_inst_1777_);
v___f_1786_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1786_, 0, v_toPure_1782_);
lean_closure_set(v___f_1786_, 1, v_f_1778_);
lean_closure_set(v___f_1786_, 2, v_toBind_1781_);
lean_closure_set(v___f_1786_, 3, v_inst_1777_);
lean_closure_set(v___f_1786_, 4, v___f_1785_);
v_sz_1787_ = lean_array_size(v_es_1783_);
v___x_1788_ = ((size_t)0ULL);
v___x_1789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1777_, v___f_1786_, v_sz_1787_, v___x_1788_, v_es_1783_);
v___x_1790_ = lean_apply_4(v_toBind_1781_, lean_box(0), lean_box(0), v___x_1789_, v___f_1784_);
return v___x_1790_;
}
else
{
lean_object* v_toApplicative_1791_; lean_object* v_toBind_1792_; lean_object* v_toPure_1793_; lean_object* v_ks_1794_; lean_object* v_vs_1795_; lean_object* v___f_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v_toApplicative_1791_ = lean_ctor_get(v_inst_1777_, 0);
v_toBind_1792_ = lean_ctor_get(v_inst_1777_, 1);
lean_inc(v_toBind_1792_);
v_toPure_1793_ = lean_ctor_get(v_toApplicative_1791_, 1);
v_ks_1794_ = lean_ctor_get(v_n_1779_, 0);
lean_inc_ref(v_ks_1794_);
v_vs_1795_ = lean_ctor_get(v_n_1779_, 1);
lean_inc_ref(v_vs_1795_);
lean_dec_ref_known(v_n_1779_, 2);
lean_inc(v_toPure_1793_);
v___f_1796_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__4), 3, 2);
lean_closure_set(v___f_1796_, 0, v_ks_1794_);
lean_closure_set(v___f_1796_, 1, v_toPure_1793_);
v___x_1797_ = l_Array_mapM_x27___redArg(v_inst_1777_, v_f_1778_, v_vs_1795_);
v___x_1798_ = lean_apply_4(v_toBind_1792_, lean_box(0), lean_box(0), v___x_1797_, v___f_1796_);
return v___x_1798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__3(lean_object* v_toPure_1799_, lean_object* v_f_1800_, lean_object* v_toBind_1801_, lean_object* v_inst_1802_, lean_object* v___f_1803_, lean_object* v_x_1804_){
_start:
{
switch(lean_obj_tag(v_x_1804_))
{
case 0:
{
lean_object* v_key_1805_; lean_object* v_val_1806_; lean_object* v___f_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v___f_1803_);
lean_dec_ref(v_inst_1802_);
v_key_1805_ = lean_ctor_get(v_x_1804_, 0);
lean_inc(v_key_1805_);
v_val_1806_ = lean_ctor_get(v_x_1804_, 1);
lean_inc(v_val_1806_);
lean_dec_ref_known(v_x_1804_, 2);
v___f_1807_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1807_, 0, v_key_1805_);
lean_closure_set(v___f_1807_, 1, v_toPure_1799_);
v___x_1808_ = lean_apply_1(v_f_1800_, v_val_1806_);
v___x_1809_ = lean_apply_4(v_toBind_1801_, lean_box(0), lean_box(0), v___x_1808_, v___f_1807_);
return v___x_1809_;
}
case 1:
{
lean_object* v_node_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_dec(v_toPure_1799_);
v_node_1810_ = lean_ctor_get(v_x_1804_, 0);
lean_inc(v_node_1810_);
lean_dec_ref_known(v_x_1804_, 1);
v___x_1811_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1802_, v_f_1800_, v_node_1810_);
v___x_1812_ = lean_apply_4(v_toBind_1801_, lean_box(0), lean_box(0), v___x_1811_, v___f_1803_);
return v___x_1812_;
}
default: 
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_dec(v___f_1803_);
lean_dec_ref(v_inst_1802_);
lean_dec(v_toBind_1801_);
lean_dec(v_f_1800_);
v___x_1813_ = lean_box(2);
v___x_1814_ = lean_apply_2(v_toPure_1799_, lean_box(0), v___x_1813_);
return v___x_1814_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux(lean_object* v_00_u03b1_1815_, lean_object* v_00_u03b2_1816_, lean_object* v_00_u03c3_1817_, lean_object* v_m_1818_, lean_object* v_inst_1819_, lean_object* v_f_1820_, lean_object* v_n_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1819_, v_f_1820_, v_n_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg___lam__0(lean_object* v_toPure_1823_, lean_object* v_root_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_apply_2(v_toPure_1823_, lean_box(0), v_root_1824_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object* v_inst_1826_, lean_object* v_pm_1827_, lean_object* v_f_1828_){
_start:
{
lean_object* v_toApplicative_1829_; lean_object* v_toBind_1830_; lean_object* v_toPure_1831_; lean_object* v___x_1832_; lean_object* v___f_1833_; lean_object* v___x_1834_; 
v_toApplicative_1829_ = lean_ctor_get(v_inst_1826_, 0);
v_toBind_1830_ = lean_ctor_get(v_inst_1826_, 1);
lean_inc(v_toBind_1830_);
v_toPure_1831_ = lean_ctor_get(v_toApplicative_1829_, 1);
lean_inc(v_toPure_1831_);
v___x_1832_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1826_, v_f_1828_, v_pm_1827_);
v___f_1833_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1833_, 0, v_toPure_1831_);
v___x_1834_ = lean_apply_4(v_toBind_1830_, lean_box(0), lean_box(0), v___x_1832_, v___f_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM(lean_object* v_00_u03b1_1835_, lean_object* v_00_u03b2_1836_, lean_object* v_00_u03c3_1837_, lean_object* v_m_1838_, lean_object* v_inst_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_pm_1842_, lean_object* v_f_1843_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_1839_, v_pm_1842_, v_f_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___boxed(lean_object* v_00_u03b1_1845_, lean_object* v_00_u03b2_1846_, lean_object* v_00_u03c3_1847_, lean_object* v_m_1848_, lean_object* v_inst_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_, lean_object* v_pm_1852_, lean_object* v_f_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_PersistentHashMap_mapM(v_00_u03b1_1845_, v_00_u03b2_1846_, v_00_u03c3_1847_, v_m_1848_, v_inst_1849_, v_x_1850_, v_x_1851_, v_pm_1852_, v_f_1853_);
lean_dec_ref(v_x_1851_);
lean_dec_ref(v_x_1850_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg___lam__0(lean_object* v_f_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_apply_1(v_f_1855_, v_x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg(lean_object* v_pm_1858_, lean_object* v_f_1859_){
_start:
{
lean_object* v___f_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___f_1860_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1860_, 0, v_f_1859_);
v___x_1861_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1862_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_1861_, v_pm_1858_, v___f_1860_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map(lean_object* v_00_u03b1_1863_, lean_object* v_00_u03b2_1864_, lean_object* v_00_u03c3_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_, lean_object* v_pm_1868_, lean_object* v_f_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_PersistentHashMap_map___redArg(v_pm_1868_, v_f_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_00_u03c3_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_, lean_object* v_pm_1876_, lean_object* v_f_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_PersistentHashMap_map(v_00_u03b1_1871_, v_00_u03b2_1872_, v_00_u03c3_1873_, v_x_1874_, v_x_1875_, v_pm_1876_, v_f_1877_);
lean_dec_ref(v_x_1875_);
lean_dec_ref(v_x_1874_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg___lam__0(lean_object* v_ps_1879_, lean_object* v_k_1880_, lean_object* v_v_1881_){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1882_, 0, v_k_1880_);
lean_ctor_set(v___x_1882_, 1, v_v_1881_);
v___x_1883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v_ps_1879_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg(lean_object* v_m_1885_){
_start:
{
lean_object* v___f_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___f_1886_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___redArg___closed__0));
v___x_1887_ = lean_box(0);
v___x_1888_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1885_, v___f_1886_, v___x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList(lean_object* v_00_u03b1_1889_, lean_object* v_00_u03b2_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v_m_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_PersistentHashMap_toList___redArg(v_m_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___boxed(lean_object* v_00_u03b1_1895_, lean_object* v_00_u03b2_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v_m_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_PersistentHashMap_toList(v_00_u03b1_1895_, v_00_u03b2_1896_, v_x_1897_, v_x_1898_, v_m_1899_);
lean_dec_ref(v_x_1898_);
lean_dec_ref(v_x_1897_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg___lam__0(lean_object* v_ps_1901_, lean_object* v_k_1902_, lean_object* v_v_1903_){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_k_1902_);
lean_ctor_set(v___x_1904_, 1, v_v_1903_);
v___x_1905_ = lean_array_push(v_ps_1901_, v___x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg(lean_object* v_m_1909_){
_start:
{
lean_object* v___f_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___f_1910_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__0));
v___x_1911_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__1));
v___x_1912_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1909_, v___f_1910_, v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray(lean_object* v_00_u03b1_1913_, lean_object* v_00_u03b2_1914_, lean_object* v_x_1915_, lean_object* v_x_1916_, lean_object* v_m_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_PersistentHashMap_toArray___redArg(v_m_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___boxed(lean_object* v_00_u03b1_1919_, lean_object* v_00_u03b2_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_m_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_PersistentHashMap_toArray(v_00_u03b1_1919_, v_00_u03b2_1920_, v_x_1921_, v_x_1922_, v_m_1923_);
lean_dec_ref(v_x_1922_);
lean_dec_ref(v_x_1921_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg(lean_object* v_x_1925_, lean_object* v_x_1926_, lean_object* v_x_1927_){
_start:
{
if (lean_obj_tag(v_x_1925_) == 0)
{
lean_object* v_es_1928_; lean_object* v_numNodes_1929_; lean_object* v_numNull_1930_; lean_object* v_numCollisions_1931_; lean_object* v_maxDepth_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1954_; 
v_es_1928_ = lean_ctor_get(v_x_1925_, 0);
v_numNodes_1929_ = lean_ctor_get(v_x_1926_, 0);
v_numNull_1930_ = lean_ctor_get(v_x_1926_, 1);
v_numCollisions_1931_ = lean_ctor_get(v_x_1926_, 2);
v_maxDepth_1932_ = lean_ctor_get(v_x_1926_, 3);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_x_1926_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1934_ = v_x_1926_;
v_isShared_1935_ = v_isSharedCheck_1954_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_maxDepth_1932_);
lean_inc(v_numCollisions_1931_);
lean_inc(v_numNull_1930_);
lean_inc(v_numNodes_1929_);
lean_dec(v_x_1926_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1954_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___y_1939_; uint8_t v___x_1953_; 
v___x_1936_ = lean_unsigned_to_nat(1u);
v___x_1937_ = lean_nat_add(v_numNodes_1929_, v___x_1936_);
lean_dec(v_numNodes_1929_);
v___x_1953_ = lean_nat_dec_le(v_maxDepth_1932_, v_x_1927_);
if (v___x_1953_ == 0)
{
v___y_1939_ = v_maxDepth_1932_;
goto v___jp_1938_;
}
else
{
lean_dec(v_maxDepth_1932_);
lean_inc(v_x_1927_);
v___y_1939_ = v_x_1927_;
goto v___jp_1938_;
}
v___jp_1938_:
{
lean_object* v_stats_1941_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 3, v___y_1939_);
lean_ctor_set(v___x_1934_, 0, v___x_1937_);
v_stats_1941_ = v___x_1934_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_numNull_1930_);
lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_numCollisions_1931_);
lean_ctor_set(v_reuseFailAlloc_1952_, 3, v___y_1939_);
v_stats_1941_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1942_ = lean_unsigned_to_nat(0u);
v___x_1943_ = lean_array_get_size(v_es_1928_);
v___x_1944_ = lean_nat_dec_lt(v___x_1942_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_dec(v_x_1927_);
return v_stats_1941_;
}
else
{
uint8_t v___x_1945_; 
v___x_1945_ = lean_nat_dec_le(v___x_1943_, v___x_1943_);
if (v___x_1945_ == 0)
{
if (v___x_1944_ == 0)
{
lean_dec(v_x_1927_);
return v_stats_1941_;
}
else
{
size_t v___x_1946_; size_t v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = ((size_t)0ULL);
v___x_1947_ = lean_usize_of_nat(v___x_1943_);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1927_, v_es_1928_, v___x_1946_, v___x_1947_, v_stats_1941_);
lean_dec(v_x_1927_);
return v___x_1948_;
}
}
else
{
size_t v___x_1949_; size_t v___x_1950_; lean_object* v___x_1951_; 
v___x_1949_ = ((size_t)0ULL);
v___x_1950_ = lean_usize_of_nat(v___x_1943_);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1927_, v_es_1928_, v___x_1949_, v___x_1950_, v_stats_1941_);
lean_dec(v_x_1927_);
return v___x_1951_;
}
}
}
}
}
}
else
{
lean_object* v_ks_1955_; lean_object* v_numNodes_1956_; lean_object* v_numNull_1957_; lean_object* v_numCollisions_1958_; lean_object* v_maxDepth_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1975_; 
v_ks_1955_ = lean_ctor_get(v_x_1925_, 0);
v_numNodes_1956_ = lean_ctor_get(v_x_1926_, 0);
v_numNull_1957_ = lean_ctor_get(v_x_1926_, 1);
v_numCollisions_1958_ = lean_ctor_get(v_x_1926_, 2);
v_maxDepth_1959_ = lean_ctor_get(v_x_1926_, 3);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_x_1926_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1961_ = v_x_1926_;
v_isShared_1962_ = v_isSharedCheck_1975_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_maxDepth_1959_);
lean_inc(v_numCollisions_1958_);
lean_inc(v_numNull_1957_);
lean_inc(v_numNodes_1956_);
lean_dec(v_x_1926_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1975_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1963_ = lean_unsigned_to_nat(1u);
v___x_1964_ = lean_nat_add(v_numNodes_1956_, v___x_1963_);
lean_dec(v_numNodes_1956_);
v___x_1965_ = lean_array_get_size(v_ks_1955_);
v___x_1966_ = lean_nat_add(v_numCollisions_1958_, v___x_1965_);
lean_dec(v_numCollisions_1958_);
v___x_1967_ = lean_nat_sub(v___x_1966_, v___x_1963_);
lean_dec(v___x_1966_);
v___x_1968_ = lean_nat_dec_le(v_maxDepth_1959_, v_x_1927_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1970_; 
lean_dec(v_x_1927_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 2, v___x_1967_);
lean_ctor_set(v___x_1961_, 0, v___x_1964_);
v___x_1970_ = v___x_1961_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1971_, 1, v_numNull_1957_);
lean_ctor_set(v_reuseFailAlloc_1971_, 2, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1971_, 3, v_maxDepth_1959_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
else
{
lean_object* v___x_1973_; 
lean_dec(v_maxDepth_1959_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 3, v_x_1927_);
lean_ctor_set(v___x_1961_, 2, v___x_1967_);
lean_ctor_set(v___x_1961_, 0, v___x_1964_);
v___x_1973_ = v___x_1961_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1964_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_numNull_1957_);
lean_ctor_set(v_reuseFailAlloc_1974_, 2, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1974_, 3, v_x_1927_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(lean_object* v_x_1976_, lean_object* v_as_1977_, size_t v_i_1978_, size_t v_stop_1979_, lean_object* v_b_1980_){
_start:
{
lean_object* v___y_1982_; uint8_t v___x_1986_; 
v___x_1986_ = lean_usize_dec_eq(v_i_1978_, v_stop_1979_);
if (v___x_1986_ == 0)
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = lean_array_uget_borrowed(v_as_1977_, v_i_1978_);
switch(lean_obj_tag(v___x_1988_))
{
case 0:
{
v___y_1982_ = v_b_1980_;
goto v___jp_1981_;
}
case 1:
{
lean_object* v_node_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_node_1989_ = lean_ctor_get(v___x_1988_, 0);
v___x_1990_ = lean_nat_add(v_x_1976_, v___x_1987_);
v___x_1991_ = l_Lean_PersistentHashMap_collectStats___redArg(v_node_1989_, v_b_1980_, v___x_1990_);
v___y_1982_ = v___x_1991_;
goto v___jp_1981_;
}
default: 
{
lean_object* v_numNodes_1992_; lean_object* v_numNull_1993_; lean_object* v_numCollisions_1994_; lean_object* v_maxDepth_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2003_; 
v_numNodes_1992_ = lean_ctor_get(v_b_1980_, 0);
v_numNull_1993_ = lean_ctor_get(v_b_1980_, 1);
v_numCollisions_1994_ = lean_ctor_get(v_b_1980_, 2);
v_maxDepth_1995_ = lean_ctor_get(v_b_1980_, 3);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_b_1980_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1997_ = v_b_1980_;
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_maxDepth_1995_);
lean_inc(v_numCollisions_1994_);
lean_inc(v_numNull_1993_);
lean_inc(v_numNodes_1992_);
lean_dec(v_b_1980_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2003_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_nat_add(v_numNull_1993_, v___x_1987_);
lean_dec(v_numNull_1993_);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 1, v___x_1999_);
v___x_2001_ = v___x_1997_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_numNodes_1992_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_numCollisions_1994_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v_maxDepth_1995_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
v___y_1982_ = v___x_2001_;
goto v___jp_1981_;
}
}
}
}
}
else
{
return v_b_1980_;
}
v___jp_1981_:
{
size_t v___x_1983_; size_t v___x_1984_; 
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1978_, v___x_1983_);
v_i_1978_ = v___x_1984_;
v_b_1980_ = v___y_1982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg___boxed(lean_object* v_x_2004_, lean_object* v_as_2005_, lean_object* v_i_2006_, lean_object* v_stop_2007_, lean_object* v_b_2008_){
_start:
{
size_t v_i_boxed_2009_; size_t v_stop_boxed_2010_; lean_object* v_res_2011_; 
v_i_boxed_2009_ = lean_unbox_usize(v_i_2006_);
lean_dec(v_i_2006_);
v_stop_boxed_2010_ = lean_unbox_usize(v_stop_2007_);
lean_dec(v_stop_2007_);
v_res_2011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2004_, v_as_2005_, v_i_boxed_2009_, v_stop_boxed_2010_, v_b_2008_);
lean_dec_ref(v_as_2005_);
lean_dec(v_x_2004_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg___boxed(lean_object* v_x_2012_, lean_object* v_x_2013_, lean_object* v_x_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2012_, v_x_2013_, v_x_2014_);
lean_dec_ref(v_x_2012_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats(lean_object* v_00_u03b1_2016_, lean_object* v_00_u03b2_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2018_, v_x_2019_, v_x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_00_u03b2_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Lean_PersistentHashMap_collectStats(v_00_u03b1_2022_, v_00_u03b2_2023_, v_x_2024_, v_x_2025_, v_x_2026_);
lean_dec_ref(v_x_2024_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(lean_object* v_00_u03b1_2028_, lean_object* v_00_u03b2_2029_, lean_object* v_x_2030_, lean_object* v_as_2031_, size_t v_i_2032_, size_t v_stop_2033_, lean_object* v_b_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2030_, v_as_2031_, v_i_2032_, v_stop_2033_, v_b_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2036_, lean_object* v_00_u03b2_2037_, lean_object* v_x_2038_, lean_object* v_as_2039_, lean_object* v_i_2040_, lean_object* v_stop_2041_, lean_object* v_b_2042_){
_start:
{
size_t v_i_boxed_2043_; size_t v_stop_boxed_2044_; lean_object* v_res_2045_; 
v_i_boxed_2043_ = lean_unbox_usize(v_i_2040_);
lean_dec(v_i_2040_);
v_stop_boxed_2044_ = lean_unbox_usize(v_stop_2041_);
lean_dec(v_stop_2041_);
v_res_2045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(v_00_u03b1_2036_, v_00_u03b2_2037_, v_x_2038_, v_as_2039_, v_i_boxed_2043_, v_stop_boxed_2044_, v_b_2042_);
lean_dec_ref(v_as_2039_);
lean_dec(v_x_2038_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg(lean_object* v_m_2048_){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = ((lean_object*)(l_Lean_PersistentHashMap_stats___redArg___closed__0));
v___x_2050_ = lean_unsigned_to_nat(1u);
v___x_2051_ = l_Lean_PersistentHashMap_collectStats___redArg(v_m_2048_, v___x_2049_, v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg___boxed(lean_object* v_m_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2052_);
lean_dec_ref(v_m_2052_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats(lean_object* v_00_u03b1_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_, lean_object* v_m_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___boxed(lean_object* v_00_u03b1_2060_, lean_object* v_00_u03b2_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_, lean_object* v_m_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_PersistentHashMap_stats(v_00_u03b1_2060_, v_00_u03b2_2061_, v_x_2062_, v_x_2063_, v_m_2064_);
lean_dec_ref(v_m_2064_);
lean_dec_ref(v_x_2063_);
lean_dec_ref(v_x_2062_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Stats_toString(lean_object* v_s_2071_){
_start:
{
lean_object* v_numNodes_2072_; lean_object* v_numNull_2073_; lean_object* v_numCollisions_2074_; lean_object* v_maxDepth_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v_numNodes_2072_ = lean_ctor_get(v_s_2071_, 0);
lean_inc(v_numNodes_2072_);
v_numNull_2073_ = lean_ctor_get(v_s_2071_, 1);
lean_inc(v_numNull_2073_);
v_numCollisions_2074_ = lean_ctor_get(v_s_2071_, 2);
lean_inc(v_numCollisions_2074_);
v_maxDepth_2075_ = lean_ctor_get(v_s_2071_, 3);
lean_inc(v_maxDepth_2075_);
lean_dec_ref(v_s_2071_);
v___x_2076_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__0));
v___x_2077_ = l_Nat_reprFast(v_numNodes_2072_);
v___x_2078_ = lean_string_append(v___x_2076_, v___x_2077_);
lean_dec_ref(v___x_2077_);
v___x_2079_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__1));
v___x_2080_ = lean_string_append(v___x_2078_, v___x_2079_);
v___x_2081_ = l_Nat_reprFast(v_numNull_2073_);
v___x_2082_ = lean_string_append(v___x_2080_, v___x_2081_);
lean_dec_ref(v___x_2081_);
v___x_2083_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__2));
v___x_2084_ = lean_string_append(v___x_2082_, v___x_2083_);
v___x_2085_ = l_Nat_reprFast(v_numCollisions_2074_);
v___x_2086_ = lean_string_append(v___x_2084_, v___x_2085_);
lean_dec_ref(v___x_2085_);
v___x_2087_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__3));
v___x_2088_ = lean_string_append(v___x_2086_, v___x_2087_);
v___x_2089_ = l_Nat_reprFast(v_maxDepth_2075_);
v___x_2090_ = lean_string_append(v___x_2088_, v___x_2089_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__4));
v___x_2092_ = lean_string_append(v___x_2090_, v___x_2091_);
return v___x_2092_;
}
}
lean_object* runtime_initialize_Init_Data_Array_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_PersistentHashMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
