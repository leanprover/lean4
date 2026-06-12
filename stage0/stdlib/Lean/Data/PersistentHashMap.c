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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
static size_t l_Lean_PersistentHashMap_insertAux___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___redArg___closed__2;
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__0(void){
_start:
{
size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; 
v___x_369_ = ((size_t)5ULL);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_shift_left(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1(void){
_start:
{
size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; 
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__0);
v___x_374_ = lean_usize_sub(v___x_373_, v___x_372_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__2(void){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg(lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_x_378_, size_t v_x_379_, size_t v_x_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
if (lean_obj_tag(v_x_378_) == 0)
{
lean_object* v_es_383_; size_t v___x_384_; size_t v___x_385_; size_t v___x_386_; size_t v___x_387_; lean_object* v_j_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_es_383_ = lean_ctor_get(v_x_378_, 0);
v___x_384_ = ((size_t)5ULL);
v___x_385_ = ((size_t)1ULL);
v___x_386_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_387_ = lean_usize_land(v_x_379_, v___x_386_);
v_j_388_ = lean_usize_to_nat(v___x_387_);
v___x_389_ = lean_array_get_size(v_es_383_);
v___x_390_ = lean_nat_dec_lt(v_j_388_, v___x_389_);
if (v___x_390_ == 0)
{
lean_dec(v_j_388_);
lean_dec(v_x_382_);
lean_dec(v_x_381_);
lean_dec_ref(v_inst_377_);
lean_dec_ref(v_inst_376_);
return v_x_378_;
}
else
{
lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_428_; 
lean_inc_ref(v_es_383_);
v_isSharedCheck_428_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_428_ == 0)
{
lean_object* v_unused_429_; 
v_unused_429_ = lean_ctor_get(v_x_378_, 0);
lean_dec(v_unused_429_);
v___x_392_ = v_x_378_;
v_isShared_393_ = v_isSharedCheck_428_;
goto v_resetjp_391_;
}
else
{
lean_dec(v_x_378_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_428_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_v_394_; lean_object* v___x_395_; lean_object* v_xs_x27_396_; lean_object* v___y_398_; 
v_v_394_ = lean_array_fget(v_es_383_, v_j_388_);
v___x_395_ = lean_box(0);
v_xs_x27_396_ = lean_array_fset(v_es_383_, v_j_388_, v___x_395_);
switch(lean_obj_tag(v_v_394_))
{
case 0:
{
lean_object* v_key_403_; lean_object* v_val_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v_inst_377_);
v_key_403_ = lean_ctor_get(v_v_394_, 0);
v_val_404_ = lean_ctor_get(v_v_394_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v_v_394_);
if (v_isSharedCheck_415_ == 0)
{
v___x_406_ = v_v_394_;
v_isShared_407_ = v_isSharedCheck_415_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_val_404_);
lean_inc(v_key_403_);
lean_dec(v_v_394_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_415_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; uint8_t v___x_409_; 
lean_inc(v_key_403_);
lean_inc(v_x_381_);
v___x_408_ = lean_apply_2(v_inst_376_, v_x_381_, v_key_403_);
v___x_409_ = lean_unbox(v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; 
lean_del_object(v___x_406_);
v___x_410_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_403_, v_val_404_, v_x_381_, v_x_382_);
v___x_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
v___y_398_ = v___x_411_;
goto v___jp_397_;
}
else
{
lean_object* v___x_413_; 
lean_dec(v_val_404_);
lean_dec(v_key_403_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v_x_382_);
lean_ctor_set(v___x_406_, 0, v_x_381_);
v___x_413_ = v___x_406_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_x_381_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_x_382_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
v___y_398_ = v___x_413_;
goto v___jp_397_;
}
}
}
}
case 1:
{
lean_object* v_node_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_426_; 
v_node_416_ = lean_ctor_get(v_v_394_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v_v_394_);
if (v_isSharedCheck_426_ == 0)
{
v___x_418_ = v_v_394_;
v_isShared_419_ = v_isSharedCheck_426_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_node_416_);
lean_dec(v_v_394_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_426_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
size_t v___x_420_; size_t v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_420_ = lean_usize_shift_right(v_x_379_, v___x_384_);
v___x_421_ = lean_usize_add(v_x_380_, v___x_385_);
v___x_422_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_376_, v_inst_377_, v_node_416_, v___x_420_, v___x_421_, v_x_381_, v_x_382_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_422_);
v___x_424_ = v___x_418_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
v___y_398_ = v___x_424_;
goto v___jp_397_;
}
}
}
default: 
{
lean_object* v___x_427_; 
lean_dec_ref(v_inst_377_);
lean_dec_ref(v_inst_376_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v_x_381_);
lean_ctor_set(v___x_427_, 1, v_x_382_);
v___y_398_ = v___x_427_;
goto v___jp_397_;
}
}
v___jp_397_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_array_fset(v_xs_x27_396_, v_j_388_, v___y_398_);
lean_dec(v_j_388_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_399_);
v___x_401_ = v___x_392_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
else
{
lean_object* v_ks_430_; lean_object* v_vs_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_451_; 
v_ks_430_ = lean_ctor_get(v_x_378_, 0);
v_vs_431_ = lean_ctor_get(v_x_378_, 1);
v_isSharedCheck_451_ = !lean_is_exclusive(v_x_378_);
if (v_isSharedCheck_451_ == 0)
{
v___x_433_ = v_x_378_;
v_isShared_434_ = v_isSharedCheck_451_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_vs_431_);
lean_inc(v_ks_430_);
lean_dec(v_x_378_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_451_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_436_; 
if (v_isShared_434_ == 0)
{
v___x_436_ = v___x_433_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_ks_430_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_vs_431_);
v___x_436_ = v_reuseFailAlloc_450_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v_newNode_437_; uint8_t v___y_439_; size_t v___x_445_; uint8_t v___x_446_; 
lean_inc_ref(v_inst_376_);
v_newNode_437_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(v_inst_376_, v___x_436_, v_x_381_, v_x_382_);
v___x_445_ = ((size_t)7ULL);
v___x_446_ = lean_usize_dec_le(v___x_445_, v_x_380_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_447_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_437_);
v___x_448_ = lean_unsigned_to_nat(4u);
v___x_449_ = lean_nat_dec_lt(v___x_447_, v___x_448_);
lean_dec(v___x_447_);
v___y_439_ = v___x_449_;
goto v___jp_438_;
}
else
{
v___y_439_ = v___x_446_;
goto v___jp_438_;
}
v___jp_438_:
{
if (v___y_439_ == 0)
{
lean_object* v_ks_440_; lean_object* v_vs_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_ks_440_ = lean_ctor_get(v_newNode_437_, 0);
lean_inc_ref(v_ks_440_);
v_vs_441_ = lean_ctor_get(v_newNode_437_, 1);
lean_inc_ref(v_vs_441_);
lean_dec_ref(v_newNode_437_);
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__2);
v___x_444_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_376_, v_inst_377_, v_x_380_, v_ks_440_, v_vs_441_, v___x_442_, v___x_443_);
lean_dec_ref(v_vs_441_);
lean_dec_ref(v_ks_440_);
return v___x_444_;
}
else
{
lean_dec_ref(v_inst_377_);
lean_dec_ref(v_inst_376_);
return v_newNode_437_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(lean_object* v_inst_452_, lean_object* v_inst_453_, size_t v_depth_454_, lean_object* v_keys_455_, lean_object* v_vals_456_, lean_object* v_i_457_, lean_object* v_entries_458_){
_start:
{
lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_array_get_size(v_keys_455_);
v___x_460_ = lean_nat_dec_lt(v_i_457_, v___x_459_);
if (v___x_460_ == 0)
{
lean_dec(v_i_457_);
lean_dec_ref(v_inst_453_);
lean_dec_ref(v_inst_452_);
return v_entries_458_;
}
else
{
lean_object* v_k_461_; lean_object* v_v_462_; lean_object* v___x_463_; uint64_t v___x_464_; size_t v_h_465_; size_t v___x_466_; lean_object* v___x_467_; size_t v___x_468_; size_t v___x_469_; size_t v___x_470_; size_t v_h_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_k_461_ = lean_array_fget_borrowed(v_keys_455_, v_i_457_);
v_v_462_ = lean_array_fget_borrowed(v_vals_456_, v_i_457_);
lean_inc_ref_n(v_inst_453_, 2);
lean_inc_n(v_k_461_, 2);
v___x_463_ = lean_apply_1(v_inst_453_, v_k_461_);
v___x_464_ = lean_unbox_uint64(v___x_463_);
lean_dec_ref(v___x_463_);
v_h_465_ = lean_uint64_to_usize(v___x_464_);
v___x_466_ = ((size_t)5ULL);
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = ((size_t)1ULL);
v___x_469_ = lean_usize_sub(v_depth_454_, v___x_468_);
v___x_470_ = lean_usize_mul(v___x_466_, v___x_469_);
v_h_471_ = lean_usize_shift_right(v_h_465_, v___x_470_);
v___x_472_ = lean_nat_add(v_i_457_, v___x_467_);
lean_dec(v_i_457_);
lean_inc(v_v_462_);
lean_inc_ref(v_inst_452_);
v___x_473_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_452_, v_inst_453_, v_entries_458_, v_h_471_, v_depth_454_, v_k_461_, v_v_462_);
v_i_457_ = v___x_472_;
v_entries_458_ = v___x_473_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg___boxed(lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_depth_477_, lean_object* v_keys_478_, lean_object* v_vals_479_, lean_object* v_i_480_, lean_object* v_entries_481_){
_start:
{
size_t v_depth_boxed_482_; lean_object* v_res_483_; 
v_depth_boxed_482_ = lean_unbox_usize(v_depth_477_);
lean_dec(v_depth_477_);
v_res_483_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_475_, v_inst_476_, v_depth_boxed_482_, v_keys_478_, v_vals_479_, v_i_480_, v_entries_481_);
lean_dec_ref(v_vals_479_);
lean_dec_ref(v_keys_478_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg___boxed(lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_x_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
size_t v_x_475__boxed_491_; size_t v_x_476__boxed_492_; lean_object* v_res_493_; 
v_x_475__boxed_491_ = lean_unbox_usize(v_x_487_);
lean_dec(v_x_487_);
v_x_476__boxed_492_ = lean_unbox_usize(v_x_488_);
lean_dec(v_x_488_);
v_res_493_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_484_, v_inst_485_, v_x_486_, v_x_475__boxed_491_, v_x_476__boxed_492_, v_x_489_, v_x_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, size_t v_depth_498_, lean_object* v_keys_499_, lean_object* v_vals_500_, lean_object* v_heq_501_, lean_object* v_i_502_, lean_object* v_entries_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_496_, v_inst_497_, v_depth_498_, v_keys_499_, v_vals_500_, v_i_502_, v_entries_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___boxed(lean_object* v_00_u03b1_505_, lean_object* v_00_u03b2_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_depth_509_, lean_object* v_keys_510_, lean_object* v_vals_511_, lean_object* v_heq_512_, lean_object* v_i_513_, lean_object* v_entries_514_){
_start:
{
size_t v_depth_boxed_515_; lean_object* v_res_516_; 
v_depth_boxed_515_ = lean_unbox_usize(v_depth_509_);
lean_dec(v_depth_509_);
v_res_516_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(v_00_u03b1_505_, v_00_u03b2_506_, v_inst_507_, v_inst_508_, v_depth_boxed_515_, v_keys_510_, v_vals_511_, v_heq_512_, v_i_513_, v_entries_514_);
lean_dec_ref(v_vals_511_);
lean_dec_ref(v_keys_510_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux(lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_x_521_, size_t v_x_522_, size_t v_x_523_, lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_519_, v_inst_520_, v_x_521_, v_x_522_, v_x_523_, v_x_524_, v_x_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___boxed(lean_object* v_00_u03b1_527_, lean_object* v_00_u03b2_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
size_t v_x_659__boxed_536_; size_t v_x_660__boxed_537_; lean_object* v_res_538_; 
v_x_659__boxed_536_ = lean_unbox_usize(v_x_532_);
lean_dec(v_x_532_);
v_x_660__boxed_537_ = lean_unbox_usize(v_x_533_);
lean_dec(v_x_533_);
v_res_538_ = l_Lean_PersistentHashMap_insertAux(v_00_u03b1_527_, v_00_u03b2_528_, v_inst_529_, v_inst_530_, v_x_531_, v_x_659__boxed_536_, v_x_660__boxed_537_, v_x_534_, v_x_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object* v_x_539_, lean_object* v_x_540_, lean_object* v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
lean_object* v___x_544_; uint64_t v___x_545_; size_t v___x_546_; size_t v___x_547_; lean_object* v___x_548_; 
lean_inc_ref(v_x_540_);
lean_inc(v_x_542_);
v___x_544_ = lean_apply_1(v_x_540_, v_x_542_);
v___x_545_ = lean_unbox_uint64(v___x_544_);
lean_dec_ref(v___x_544_);
v___x_546_ = lean_uint64_to_usize(v___x_545_);
v___x_547_ = ((size_t)1ULL);
v___x_548_ = l_Lean_PersistentHashMap_insertAux___redArg(v_x_539_, v_x_540_, v_x_541_, v___x_546_, v___x_547_, v_x_542_, v_x_543_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert(lean_object* v_00_u03b1_549_, lean_object* v_00_u03b2_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_PersistentHashMap_insert___redArg(v_x_551_, v_x_552_, v_x_553_, v_x_554_, v_x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg(lean_object* v_inst_557_, lean_object* v_keys_558_, lean_object* v_vals_559_, lean_object* v_i_560_, lean_object* v_k_561_){
_start:
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_array_get_size(v_keys_558_);
v___x_563_ = lean_nat_dec_lt(v_i_560_, v___x_562_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; 
lean_dec(v_k_561_);
lean_dec(v_i_560_);
lean_dec_ref(v_inst_557_);
v___x_564_ = lean_box(0);
return v___x_564_;
}
else
{
lean_object* v_k_x27_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_k_x27_565_ = lean_array_fget_borrowed(v_keys_558_, v_i_560_);
lean_inc_ref(v_inst_557_);
lean_inc(v_k_x27_565_);
lean_inc(v_k_561_);
v___x_566_ = lean_apply_2(v_inst_557_, v_k_561_, v_k_x27_565_);
v___x_567_ = lean_unbox(v___x_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = lean_nat_add(v_i_560_, v___x_568_);
lean_dec(v_i_560_);
v_i_560_ = v___x_569_;
goto _start;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec(v_k_561_);
lean_dec_ref(v_inst_557_);
v___x_571_ = lean_array_fget_borrowed(v_vals_559_, v_i_560_);
lean_dec(v_i_560_);
lean_inc(v___x_571_);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg___boxed(lean_object* v_inst_573_, lean_object* v_keys_574_, lean_object* v_vals_575_, lean_object* v_i_576_, lean_object* v_k_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_573_, v_keys_574_, v_vals_575_, v_i_576_, v_k_577_);
lean_dec_ref(v_vals_575_);
lean_dec_ref(v_keys_574_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux(lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_inst_581_, lean_object* v_keys_582_, lean_object* v_vals_583_, lean_object* v_heq_584_, lean_object* v_i_585_, lean_object* v_k_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_581_, v_keys_582_, v_vals_583_, v_i_585_, v_k_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___boxed(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_inst_590_, lean_object* v_keys_591_, lean_object* v_vals_592_, lean_object* v_heq_593_, lean_object* v_i_594_, lean_object* v_k_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_PersistentHashMap_findAtAux(v_00_u03b1_588_, v_00_u03b2_589_, v_inst_590_, v_keys_591_, v_vals_592_, v_heq_593_, v_i_594_, v_k_595_);
lean_dec_ref(v_vals_592_);
lean_dec_ref(v_keys_591_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg(lean_object* v_inst_597_, lean_object* v_x_598_, size_t v_x_599_, lean_object* v_x_600_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
lean_object* v_es_601_; lean_object* v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; lean_object* v_j_606_; lean_object* v___x_607_; 
v_es_601_ = lean_ctor_get(v_x_598_, 0);
lean_inc_ref(v_es_601_);
lean_dec_ref_known(v_x_598_, 1);
v___x_602_ = lean_box(2);
v___x_603_ = ((size_t)5ULL);
v___x_604_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_605_ = lean_usize_land(v_x_599_, v___x_604_);
v_j_606_ = lean_usize_to_nat(v___x_605_);
v___x_607_ = lean_array_get(v___x_602_, v_es_601_, v_j_606_);
lean_dec(v_j_606_);
lean_dec_ref(v_es_601_);
switch(lean_obj_tag(v___x_607_))
{
case 0:
{
lean_object* v_key_608_; lean_object* v_val_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_key_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_key_608_);
v_val_609_ = lean_ctor_get(v___x_607_, 1);
lean_inc(v_val_609_);
lean_dec_ref_known(v___x_607_, 2);
v___x_610_ = lean_apply_2(v_inst_597_, v_x_600_, v_key_608_);
v___x_611_ = lean_unbox(v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_dec(v_val_609_);
v___x_612_ = lean_box(0);
return v___x_612_;
}
else
{
lean_object* v___x_613_; 
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_val_609_);
return v___x_613_;
}
}
case 1:
{
lean_object* v_node_614_; size_t v___x_615_; 
v_node_614_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_node_614_);
lean_dec_ref_known(v___x_607_, 1);
v___x_615_ = lean_usize_shift_right(v_x_599_, v___x_603_);
v_x_598_ = v_node_614_;
v_x_599_ = v___x_615_;
goto _start;
}
default: 
{
lean_object* v___x_617_; 
lean_dec(v_x_600_);
lean_dec_ref(v_inst_597_);
v___x_617_ = lean_box(0);
return v___x_617_;
}
}
}
else
{
lean_object* v_ks_618_; lean_object* v_vs_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_ks_618_ = lean_ctor_get(v_x_598_, 0);
lean_inc_ref(v_ks_618_);
v_vs_619_ = lean_ctor_get(v_x_598_, 1);
lean_inc_ref(v_vs_619_);
lean_dec_ref_known(v_x_598_, 2);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_597_, v_ks_618_, v_vs_619_, v___x_620_, v_x_600_);
lean_dec_ref(v_vs_619_);
lean_dec_ref(v_ks_618_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg___boxed(lean_object* v_inst_622_, lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
size_t v_x_151__boxed_626_; lean_object* v_res_627_; 
v_x_151__boxed_626_ = lean_unbox_usize(v_x_624_);
lean_dec(v_x_624_);
v_res_627_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_622_, v_x_623_, v_x_151__boxed_626_, v_x_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux(lean_object* v_00_u03b1_628_, lean_object* v_00_u03b2_629_, lean_object* v_inst_630_, lean_object* v_x_631_, size_t v_x_632_, lean_object* v_x_633_){
_start:
{
lean_object* v___x_634_; 
lean_inc_ref(v_x_631_);
v___x_634_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_630_, v_x_631_, v_x_632_, v_x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___boxed(lean_object* v_00_u03b1_635_, lean_object* v_00_u03b2_636_, lean_object* v_inst_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
size_t v_x_205__boxed_641_; lean_object* v_res_642_; 
v_x_205__boxed_641_ = lean_unbox_usize(v_x_639_);
lean_dec(v_x_639_);
v_res_642_ = l_Lean_PersistentHashMap_findAux(v_00_u03b1_635_, v_00_u03b2_636_, v_inst_637_, v_x_638_, v_x_205__boxed_641_, v_x_640_);
lean_dec_ref(v_x_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; uint64_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
lean_inc(v_x_646_);
v___x_647_ = lean_apply_1(v_x_644_, v_x_646_);
v___x_648_ = lean_unbox_uint64(v___x_647_);
lean_dec_ref(v___x_647_);
v___x_649_ = lean_uint64_to_usize(v___x_648_);
lean_inc_ref(v_x_645_);
v___x_650_ = l_Lean_PersistentHashMap_findAux___redArg(v_x_643_, v_x_645_, v___x_649_, v_x_646_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg___boxed(lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_651_, v_x_652_, v_x_653_, v_x_654_);
lean_dec_ref(v_x_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f(lean_object* v_00_u03b1_656_, lean_object* v_00_u03b2_657_, lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_658_, v_x_659_, v_x_660_, v_x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___boxed(lean_object* v_00_u03b1_663_, lean_object* v_00_u03b2_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Lean_PersistentHashMap_find_x3f(v_00_u03b1_663_, v_00_u03b2_664_, v_x_665_, v_x_666_, v_x_667_, v_x_668_);
lean_dec_ref(v_x_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_m_672_, lean_object* v_i_673_, lean_object* v_x_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_670_, v_x_671_, v_m_672_, v_i_673_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed(lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_m_678_, lean_object* v_i_679_, lean_object* v_x_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(v_x_676_, v_x_677_, v_m_678_, v_i_679_, v_x_680_);
lean_dec_ref(v_m_678_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg(lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___f_684_; 
v___f_684_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_684_, 0, v_x_682_);
lean_closure_set(v___f_684_, 1, v_x_683_);
return v___f_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue(lean_object* v_00_u03b1_685_, lean_object* v_00_u03b2_686_, lean_object* v_x_687_, lean_object* v_x_688_){
_start:
{
lean_object* v___f_689_; 
v___f_689_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_689_, 0, v_x_687_);
lean_closure_set(v___f_689_, 1, v_x_688_);
return v___f_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg(lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_m_692_, lean_object* v_a_693_, lean_object* v_b_u2080_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_690_, v_x_691_, v_m_692_, v_a_693_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_inc(v_b_u2080_694_);
return v_b_u2080_694_;
}
else
{
lean_object* v_val_696_; 
v_val_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v___x_695_, 1);
return v_val_696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg___boxed(lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_m_699_, lean_object* v_a_700_, lean_object* v_b_u2080_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_PersistentHashMap_findD___redArg(v_x_697_, v_x_698_, v_m_699_, v_a_700_, v_b_u2080_701_);
lean_dec(v_b_u2080_701_);
lean_dec_ref(v_m_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_m_707_, lean_object* v_a_708_, lean_object* v_b_u2080_709_){
_start:
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_705_, v_x_706_, v_m_707_, v_a_708_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_inc(v_b_u2080_709_);
return v_b_u2080_709_;
}
else
{
lean_object* v_val_711_; 
v_val_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_val_711_);
lean_dec_ref_known(v___x_710_, 1);
return v_val_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___boxed(lean_object* v_00_u03b1_712_, lean_object* v_00_u03b2_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_m_716_, lean_object* v_a_717_, lean_object* v_b_u2080_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_PersistentHashMap_findD(v_00_u03b1_712_, v_00_u03b2_713_, v_x_714_, v_x_715_, v_m_716_, v_a_717_, v_b_u2080_718_);
lean_dec(v_b_u2080_718_);
lean_dec_ref(v_m_716_);
return v_res_719_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_723_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__2));
v___x_724_ = lean_unsigned_to_nat(14u);
v___x_725_ = lean_unsigned_to_nat(178u);
v___x_726_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__1));
v___x_727_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__0));
v___x_728_ = l_mkPanicMessageWithDecl(v___x_727_, v___x_726_, v___x_725_, v___x_724_, v___x_723_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg(lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_inst_731_, lean_object* v_m_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_729_, v_x_730_, v_m_732_, v_a_733_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_736_ = l_panic___redArg(v_inst_731_, v___x_735_);
return v___x_736_;
}
else
{
lean_object* v_val_737_; 
v_val_737_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v___x_734_, 1);
return v_val_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg___boxed(lean_object* v_x_738_, lean_object* v_x_739_, lean_object* v_inst_740_, lean_object* v_m_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_PersistentHashMap_find_x21___redArg(v_x_738_, v_x_739_, v_inst_740_, v_m_741_, v_a_742_);
lean_dec_ref(v_m_741_);
lean_dec(v_inst_740_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21(lean_object* v_00_u03b1_744_, lean_object* v_00_u03b2_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_inst_748_, lean_object* v_m_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_746_, v_x_747_, v_m_749_, v_a_750_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_753_ = l_panic___redArg(v_inst_748_, v___x_752_);
return v___x_753_;
}
else
{
lean_object* v_val_754_; 
v_val_754_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_val_754_);
lean_dec_ref_known(v___x_751_, 1);
return v_val_754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___boxed(lean_object* v_00_u03b1_755_, lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_inst_759_, lean_object* v_m_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_PersistentHashMap_find_x21(v_00_u03b1_755_, v_00_u03b2_756_, v_x_757_, v_x_758_, v_inst_759_, v_m_760_, v_a_761_);
lean_dec_ref(v_m_760_);
lean_dec(v_inst_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg(lean_object* v_inst_763_, lean_object* v_keys_764_, lean_object* v_vals_765_, lean_object* v_i_766_, lean_object* v_k_767_){
_start:
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_array_get_size(v_keys_764_);
v___x_769_ = lean_nat_dec_lt(v_i_766_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec(v_k_767_);
lean_dec(v_i_766_);
lean_dec_ref(v_inst_763_);
v___x_770_ = lean_box(0);
return v___x_770_;
}
else
{
lean_object* v_k_x27_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_k_x27_771_ = lean_array_fget_borrowed(v_keys_764_, v_i_766_);
lean_inc_ref(v_inst_763_);
lean_inc(v_k_x27_771_);
lean_inc(v_k_767_);
v___x_772_ = lean_apply_2(v_inst_763_, v_k_767_, v_k_x27_771_);
v___x_773_ = lean_unbox(v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(1u);
v___x_775_ = lean_nat_add(v_i_766_, v___x_774_);
lean_dec(v_i_766_);
v_i_766_ = v___x_775_;
goto _start;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec(v_k_767_);
lean_dec_ref(v_inst_763_);
v___x_777_ = lean_array_fget_borrowed(v_vals_765_, v_i_766_);
lean_dec(v_i_766_);
lean_inc(v___x_777_);
lean_inc(v_k_x27_771_);
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v_k_x27_771_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
v___x_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg___boxed(lean_object* v_inst_780_, lean_object* v_keys_781_, lean_object* v_vals_782_, lean_object* v_i_783_, lean_object* v_k_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_780_, v_keys_781_, v_vals_782_, v_i_783_, v_k_784_);
lean_dec_ref(v_vals_782_);
lean_dec_ref(v_keys_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux(lean_object* v_00_u03b1_786_, lean_object* v_00_u03b2_787_, lean_object* v_inst_788_, lean_object* v_keys_789_, lean_object* v_vals_790_, lean_object* v_heq_791_, lean_object* v_i_792_, lean_object* v_k_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_788_, v_keys_789_, v_vals_790_, v_i_792_, v_k_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___boxed(lean_object* v_00_u03b1_795_, lean_object* v_00_u03b2_796_, lean_object* v_inst_797_, lean_object* v_keys_798_, lean_object* v_vals_799_, lean_object* v_heq_800_, lean_object* v_i_801_, lean_object* v_k_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_PersistentHashMap_findEntryAtAux(v_00_u03b1_795_, v_00_u03b2_796_, v_inst_797_, v_keys_798_, v_vals_799_, v_heq_800_, v_i_801_, v_k_802_);
lean_dec_ref(v_vals_799_);
lean_dec_ref(v_keys_798_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg(lean_object* v_inst_804_, lean_object* v_x_805_, size_t v_x_806_, lean_object* v_x_807_){
_start:
{
if (lean_obj_tag(v_x_805_) == 0)
{
lean_object* v_es_808_; lean_object* v___x_809_; size_t v___x_810_; size_t v___x_811_; size_t v___x_812_; lean_object* v_j_813_; lean_object* v___x_814_; 
v_es_808_ = lean_ctor_get(v_x_805_, 0);
lean_inc_ref(v_es_808_);
lean_dec_ref_known(v_x_805_, 1);
v___x_809_ = lean_box(2);
v___x_810_ = ((size_t)5ULL);
v___x_811_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_812_ = lean_usize_land(v_x_806_, v___x_811_);
v_j_813_ = lean_usize_to_nat(v___x_812_);
v___x_814_ = lean_array_get(v___x_809_, v_es_808_, v_j_813_);
lean_dec(v_j_813_);
lean_dec_ref(v_es_808_);
switch(lean_obj_tag(v___x_814_))
{
case 0:
{
lean_object* v_key_815_; lean_object* v_val_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_key_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc_n(v_key_815_, 2);
v_val_816_ = lean_ctor_get(v___x_814_, 1);
lean_inc(v_val_816_);
lean_dec_ref_known(v___x_814_, 2);
v___x_817_ = lean_apply_2(v_inst_804_, v_x_807_, v_key_815_);
v___x_818_ = lean_unbox(v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
lean_dec(v_val_816_);
lean_dec(v_key_815_);
v___x_819_ = lean_box(0);
return v___x_819_;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_key_815_);
lean_ctor_set(v___x_820_, 1, v_val_816_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
case 1:
{
lean_object* v_node_822_; size_t v___x_823_; 
v_node_822_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_node_822_);
lean_dec_ref_known(v___x_814_, 1);
v___x_823_ = lean_usize_shift_right(v_x_806_, v___x_810_);
v_x_805_ = v_node_822_;
v_x_806_ = v___x_823_;
goto _start;
}
default: 
{
lean_object* v___x_825_; 
lean_dec(v_x_807_);
lean_dec_ref(v_inst_804_);
v___x_825_ = lean_box(0);
return v___x_825_;
}
}
}
else
{
lean_object* v_ks_826_; lean_object* v_vs_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_ks_826_ = lean_ctor_get(v_x_805_, 0);
lean_inc_ref(v_ks_826_);
v_vs_827_ = lean_ctor_get(v_x_805_, 1);
lean_inc_ref(v_vs_827_);
lean_dec_ref_known(v_x_805_, 2);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_804_, v_ks_826_, v_vs_827_, v___x_828_, v_x_807_);
lean_dec_ref(v_vs_827_);
lean_dec_ref(v_ks_826_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg___boxed(lean_object* v_inst_830_, lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
size_t v_x_155__boxed_834_; lean_object* v_res_835_; 
v_x_155__boxed_834_ = lean_unbox_usize(v_x_832_);
lean_dec(v_x_832_);
v_res_835_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_830_, v_x_831_, v_x_155__boxed_834_, v_x_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux(lean_object* v_00_u03b1_836_, lean_object* v_00_u03b2_837_, lean_object* v_inst_838_, lean_object* v_x_839_, size_t v_x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v___x_842_; 
lean_inc_ref(v_x_839_);
v___x_842_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_838_, v_x_839_, v_x_840_, v_x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___boxed(lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_inst_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
size_t v_x_211__boxed_849_; lean_object* v_res_850_; 
v_x_211__boxed_849_ = lean_unbox_usize(v_x_847_);
lean_dec(v_x_847_);
v_res_850_ = l_Lean_PersistentHashMap_findEntryAux(v_00_u03b1_843_, v_00_u03b2_844_, v_inst_845_, v_x_846_, v_x_211__boxed_849_, v_x_848_);
lean_dec_ref(v_x_846_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object* v_x_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_x_854_){
_start:
{
lean_object* v___x_855_; uint64_t v___x_856_; size_t v___x_857_; lean_object* v___x_858_; 
lean_inc(v_x_854_);
v___x_855_ = lean_apply_1(v_x_852_, v_x_854_);
v___x_856_ = lean_unbox_uint64(v___x_855_);
lean_dec_ref(v___x_855_);
v___x_857_ = lean_uint64_to_usize(v___x_856_);
lean_inc_ref(v_x_853_);
v___x_858_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_x_851_, v_x_853_, v___x_857_, v_x_854_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg___boxed(lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_x_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_859_, v_x_860_, v_x_861_, v_x_862_);
lean_dec_ref(v_x_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f(lean_object* v_00_u03b1_864_, lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_866_, v_x_867_, v_x_868_, v_x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___boxed(lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_PersistentHashMap_findEntry_x3f(v_00_u03b1_871_, v_00_u03b2_872_, v_x_873_, v_x_874_, v_x_875_, v_x_876_);
lean_dec_ref(v_x_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg(lean_object* v_inst_878_, lean_object* v_keys_879_, lean_object* v_i_880_, lean_object* v_k_881_, lean_object* v_k_u2080_882_){
_start:
{
lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_883_ = lean_array_get_size(v_keys_879_);
v___x_884_ = lean_nat_dec_lt(v_i_880_, v___x_883_);
if (v___x_884_ == 0)
{
lean_dec(v_k_881_);
lean_dec(v_i_880_);
lean_dec_ref(v_inst_878_);
lean_inc(v_k_u2080_882_);
return v_k_u2080_882_;
}
else
{
lean_object* v_k_x27_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_k_x27_885_ = lean_array_fget_borrowed(v_keys_879_, v_i_880_);
lean_inc_ref(v_inst_878_);
lean_inc(v_k_x27_885_);
lean_inc(v_k_881_);
v___x_886_ = lean_apply_2(v_inst_878_, v_k_881_, v_k_x27_885_);
v___x_887_ = lean_unbox(v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; 
v___x_888_ = lean_unsigned_to_nat(1u);
v___x_889_ = lean_nat_add(v_i_880_, v___x_888_);
lean_dec(v_i_880_);
v_i_880_ = v___x_889_;
goto _start;
}
else
{
lean_dec(v_k_881_);
lean_dec(v_i_880_);
lean_dec_ref(v_inst_878_);
lean_inc(v_k_x27_885_);
return v_k_x27_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg___boxed(lean_object* v_inst_891_, lean_object* v_keys_892_, lean_object* v_i_893_, lean_object* v_k_894_, lean_object* v_k_u2080_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_891_, v_keys_892_, v_i_893_, v_k_894_, v_k_u2080_895_);
lean_dec(v_k_u2080_895_);
lean_dec_ref(v_keys_892_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux(lean_object* v_00_u03b1_897_, lean_object* v_00_u03b2_898_, lean_object* v_inst_899_, lean_object* v_keys_900_, lean_object* v_vals_901_, lean_object* v_heq_902_, lean_object* v_i_903_, lean_object* v_k_904_, lean_object* v_k_u2080_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_899_, v_keys_900_, v_i_903_, v_k_904_, v_k_u2080_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___boxed(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_inst_909_, lean_object* v_keys_910_, lean_object* v_vals_911_, lean_object* v_heq_912_, lean_object* v_i_913_, lean_object* v_k_914_, lean_object* v_k_u2080_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_PersistentHashMap_findKeyDAtAux(v_00_u03b1_907_, v_00_u03b2_908_, v_inst_909_, v_keys_910_, v_vals_911_, v_heq_912_, v_i_913_, v_k_914_, v_k_u2080_915_);
lean_dec(v_k_u2080_915_);
lean_dec_ref(v_vals_911_);
lean_dec_ref(v_keys_910_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object* v_inst_917_, lean_object* v_x_918_, size_t v_x_919_, lean_object* v_x_920_, lean_object* v_x_921_){
_start:
{
if (lean_obj_tag(v_x_918_) == 0)
{
lean_object* v_es_922_; lean_object* v___x_923_; size_t v___x_924_; size_t v___x_925_; size_t v___x_926_; lean_object* v_j_927_; lean_object* v___x_928_; 
v_es_922_ = lean_ctor_get(v_x_918_, 0);
lean_inc_ref(v_es_922_);
lean_dec_ref_known(v_x_918_, 1);
v___x_923_ = lean_box(2);
v___x_924_ = ((size_t)5ULL);
v___x_925_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_926_ = lean_usize_land(v_x_919_, v___x_925_);
v_j_927_ = lean_usize_to_nat(v___x_926_);
v___x_928_ = lean_array_get(v___x_923_, v_es_922_, v_j_927_);
lean_dec(v_j_927_);
lean_dec_ref(v_es_922_);
switch(lean_obj_tag(v___x_928_))
{
case 0:
{
lean_object* v_key_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_key_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc_n(v_key_929_, 2);
lean_dec_ref_known(v___x_928_, 2);
v___x_930_ = lean_apply_2(v_inst_917_, v_x_920_, v_key_929_);
v___x_931_ = lean_unbox(v___x_930_);
if (v___x_931_ == 0)
{
lean_dec(v_key_929_);
lean_inc(v_x_921_);
return v_x_921_;
}
else
{
return v_key_929_;
}
}
case 1:
{
lean_object* v_node_932_; size_t v___x_933_; 
v_node_932_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_node_932_);
lean_dec_ref_known(v___x_928_, 1);
v___x_933_ = lean_usize_shift_right(v_x_919_, v___x_924_);
v_x_918_ = v_node_932_;
v_x_919_ = v___x_933_;
goto _start;
}
default: 
{
lean_dec(v_x_920_);
lean_dec_ref(v_inst_917_);
lean_inc(v_x_921_);
return v_x_921_;
}
}
}
else
{
lean_object* v_ks_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_ks_935_ = lean_ctor_get(v_x_918_, 0);
lean_inc_ref(v_ks_935_);
lean_dec_ref_known(v_x_918_, 2);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_917_, v_ks_935_, v___x_936_, v_x_920_, v_x_921_);
lean_dec_ref(v_ks_935_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg___boxed(lean_object* v_inst_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_x_942_){
_start:
{
size_t v_x_140__boxed_943_; lean_object* v_res_944_; 
v_x_140__boxed_943_ = lean_unbox_usize(v_x_940_);
lean_dec(v_x_940_);
v_res_944_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_938_, v_x_939_, v_x_140__boxed_943_, v_x_941_, v_x_942_);
lean_dec(v_x_942_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux(lean_object* v_00_u03b1_945_, lean_object* v_00_u03b2_946_, lean_object* v_inst_947_, lean_object* v_x_948_, size_t v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_947_, v_x_948_, v_x_949_, v_x_950_, v_x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___boxed(lean_object* v_00_u03b1_953_, lean_object* v_00_u03b2_954_, lean_object* v_inst_955_, lean_object* v_x_956_, lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
size_t v_x_189__boxed_960_; lean_object* v_res_961_; 
v_x_189__boxed_960_ = lean_unbox_usize(v_x_957_);
lean_dec(v_x_957_);
v_res_961_ = l_Lean_PersistentHashMap_findKeyDAux(v_00_u03b1_953_, v_00_u03b2_954_, v_inst_955_, v_x_956_, v_x_189__boxed_960_, v_x_958_, v_x_959_);
lean_dec(v_x_959_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg(lean_object* v_x_962_, lean_object* v_x_963_, lean_object* v_m_964_, lean_object* v_a_965_, lean_object* v_a_u2080_966_){
_start:
{
lean_object* v___x_967_; uint64_t v___x_968_; size_t v___x_969_; lean_object* v___x_970_; 
lean_inc(v_a_965_);
v___x_967_ = lean_apply_1(v_x_963_, v_a_965_);
v___x_968_ = lean_unbox_uint64(v___x_967_);
lean_dec_ref(v___x_967_);
v___x_969_ = lean_uint64_to_usize(v___x_968_);
v___x_970_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_962_, v_m_964_, v___x_969_, v_a_965_, v_a_u2080_966_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg___boxed(lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_m_973_, lean_object* v_a_974_, lean_object* v_a_u2080_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_PersistentHashMap_findKeyD___redArg(v_x_971_, v_x_972_, v_m_973_, v_a_974_, v_a_u2080_975_);
lean_dec(v_a_u2080_975_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD(lean_object* v_00_u03b1_977_, lean_object* v_00_u03b2_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_m_981_, lean_object* v_a_982_, lean_object* v_a_u2080_983_){
_start:
{
lean_object* v___x_984_; uint64_t v___x_985_; size_t v___x_986_; lean_object* v___x_987_; 
lean_inc(v_a_982_);
v___x_984_ = lean_apply_1(v_x_980_, v_a_982_);
v___x_985_ = lean_unbox_uint64(v___x_984_);
lean_dec_ref(v___x_984_);
v___x_986_ = lean_uint64_to_usize(v___x_985_);
v___x_987_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_979_, v_m_981_, v___x_986_, v_a_982_, v_a_u2080_983_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___boxed(lean_object* v_00_u03b1_988_, lean_object* v_00_u03b2_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_m_992_, lean_object* v_a_993_, lean_object* v_a_u2080_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_PersistentHashMap_findKeyD(v_00_u03b1_988_, v_00_u03b2_989_, v_x_990_, v_x_991_, v_m_992_, v_a_993_, v_a_u2080_994_);
lean_dec(v_a_u2080_994_);
return v_res_995_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___redArg(lean_object* v_inst_996_, lean_object* v_keys_997_, lean_object* v_i_998_, lean_object* v_k_999_){
_start:
{
lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_1000_ = lean_array_get_size(v_keys_997_);
v___x_1001_ = lean_nat_dec_lt(v_i_998_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec(v_k_999_);
lean_dec(v_i_998_);
lean_dec_ref(v_inst_996_);
return v___x_1001_;
}
else
{
lean_object* v_k_x27_1002_; lean_object* v___x_1003_; uint8_t v___x_1004_; 
v_k_x27_1002_ = lean_array_fget_borrowed(v_keys_997_, v_i_998_);
lean_inc_ref(v_inst_996_);
lean_inc(v_k_x27_1002_);
lean_inc(v_k_999_);
v___x_1003_ = lean_apply_2(v_inst_996_, v_k_999_, v_k_x27_1002_);
v___x_1004_ = lean_unbox(v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_unsigned_to_nat(1u);
v___x_1006_ = lean_nat_add(v_i_998_, v___x_1005_);
lean_dec(v_i_998_);
v_i_998_ = v___x_1006_;
goto _start;
}
else
{
uint8_t v___x_1008_; 
lean_dec(v_k_999_);
lean_dec(v_i_998_);
lean_dec_ref(v_inst_996_);
v___x_1008_ = lean_unbox(v___x_1003_);
return v___x_1008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___redArg___boxed(lean_object* v_inst_1009_, lean_object* v_keys_1010_, lean_object* v_i_1011_, lean_object* v_k_1012_){
_start:
{
uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_res_1013_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1009_, v_keys_1010_, v_i_1011_, v_k_1012_);
lean_dec_ref(v_keys_1010_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux(lean_object* v_00_u03b1_1015_, lean_object* v_00_u03b2_1016_, lean_object* v_inst_1017_, lean_object* v_keys_1018_, lean_object* v_vals_1019_, lean_object* v_heq_1020_, lean_object* v_i_1021_, lean_object* v_k_1022_){
_start:
{
uint8_t v___x_1023_; 
v___x_1023_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1017_, v_keys_1018_, v_i_1021_, v_k_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___boxed(lean_object* v_00_u03b1_1024_, lean_object* v_00_u03b2_1025_, lean_object* v_inst_1026_, lean_object* v_keys_1027_, lean_object* v_vals_1028_, lean_object* v_heq_1029_, lean_object* v_i_1030_, lean_object* v_k_1031_){
_start:
{
uint8_t v_res_1032_; lean_object* v_r_1033_; 
v_res_1032_ = l_Lean_PersistentHashMap_containsAtAux(v_00_u03b1_1024_, v_00_u03b2_1025_, v_inst_1026_, v_keys_1027_, v_vals_1028_, v_heq_1029_, v_i_1030_, v_k_1031_);
lean_dec_ref(v_vals_1028_);
lean_dec_ref(v_keys_1027_);
v_r_1033_ = lean_box(v_res_1032_);
return v_r_1033_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___redArg(lean_object* v_inst_1034_, lean_object* v_x_1035_, size_t v_x_1036_, lean_object* v_x_1037_){
_start:
{
if (lean_obj_tag(v_x_1035_) == 0)
{
lean_object* v_es_1038_; lean_object* v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; lean_object* v_j_1043_; lean_object* v___x_1044_; 
v_es_1038_ = lean_ctor_get(v_x_1035_, 0);
lean_inc_ref(v_es_1038_);
lean_dec_ref_known(v_x_1035_, 1);
v___x_1039_ = lean_box(2);
v___x_1040_ = ((size_t)5ULL);
v___x_1041_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_1042_ = lean_usize_land(v_x_1036_, v___x_1041_);
v_j_1043_ = lean_usize_to_nat(v___x_1042_);
v___x_1044_ = lean_array_get(v___x_1039_, v_es_1038_, v_j_1043_);
lean_dec(v_j_1043_);
lean_dec_ref(v_es_1038_);
switch(lean_obj_tag(v___x_1044_))
{
case 0:
{
lean_object* v_key_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v_key_1045_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_key_1045_);
lean_dec_ref_known(v___x_1044_, 2);
v___x_1046_ = lean_apply_2(v_inst_1034_, v_x_1037_, v_key_1045_);
v___x_1047_ = lean_unbox(v___x_1046_);
return v___x_1047_;
}
case 1:
{
lean_object* v_node_1048_; size_t v___x_1049_; 
v_node_1048_ = lean_ctor_get(v___x_1044_, 0);
lean_inc(v_node_1048_);
lean_dec_ref_known(v___x_1044_, 1);
v___x_1049_ = lean_usize_shift_right(v_x_1036_, v___x_1040_);
v_x_1035_ = v_node_1048_;
v_x_1036_ = v___x_1049_;
goto _start;
}
default: 
{
uint8_t v___x_1051_; 
lean_dec(v_x_1037_);
lean_dec_ref(v_inst_1034_);
v___x_1051_ = 0;
return v___x_1051_;
}
}
}
else
{
lean_object* v_ks_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_ks_1052_ = lean_ctor_get(v_x_1035_, 0);
lean_inc_ref(v_ks_1052_);
lean_dec_ref_known(v_x_1035_, 2);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1034_, v_ks_1052_, v___x_1053_, v_x_1037_);
lean_dec_ref(v_ks_1052_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___redArg___boxed(lean_object* v_inst_1055_, lean_object* v_x_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
size_t v_x_110__boxed_1059_; uint8_t v_res_1060_; lean_object* v_r_1061_; 
v_x_110__boxed_1059_ = lean_unbox_usize(v_x_1057_);
lean_dec(v_x_1057_);
v_res_1060_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1055_, v_x_1056_, v_x_110__boxed_1059_, v_x_1058_);
v_r_1061_ = lean_box(v_res_1060_);
return v_r_1061_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux(lean_object* v_00_u03b1_1062_, lean_object* v_00_u03b2_1063_, lean_object* v_inst_1064_, lean_object* v_x_1065_, size_t v_x_1066_, lean_object* v_x_1067_){
_start:
{
uint8_t v___x_1068_; 
v___x_1068_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1064_, v_x_1065_, v_x_1066_, v_x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___boxed(lean_object* v_00_u03b1_1069_, lean_object* v_00_u03b2_1070_, lean_object* v_inst_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
size_t v_x_158__boxed_1075_; uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_x_158__boxed_1075_ = lean_unbox_usize(v_x_1073_);
lean_dec(v_x_1073_);
v_res_1076_ = l_Lean_PersistentHashMap_containsAux(v_00_u03b1_1069_, v_00_u03b2_1070_, v_inst_1071_, v_x_1072_, v_x_158__boxed_1075_, v_x_1074_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; uint64_t v___x_1083_; size_t v___x_1084_; uint8_t v___x_1085_; 
lean_inc(v_x_1081_);
v___x_1082_ = lean_apply_1(v_inst_1079_, v_x_1081_);
v___x_1083_ = lean_unbox_uint64(v___x_1082_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = lean_uint64_to_usize(v___x_1083_);
v___x_1085_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1078_, v_x_1080_, v___x_1084_, v_x_1081_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___redArg___boxed(lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
uint8_t v_res_1090_; lean_object* v_r_1091_; 
v_res_1090_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1086_, v_inst_1087_, v_x_1088_, v_x_1089_);
v_r_1091_ = lean_box(v_res_1090_);
return v_r_1091_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains(lean_object* v_00_u03b1_1092_, lean_object* v_00_u03b2_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
uint8_t v___x_1098_; 
v___x_1098_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1094_, v_inst_1095_, v_x_1096_, v_x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___boxed(lean_object* v_00_u03b1_1099_, lean_object* v_00_u03b2_1100_, lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
uint8_t v_res_1105_; lean_object* v_r_1106_; 
v_res_1105_ = l_Lean_PersistentHashMap_contains(v_00_u03b1_1099_, v_00_u03b2_1100_, v_inst_1101_, v_inst_1102_, v_x_1103_, v_x_1104_);
v_r_1106_ = lean_box(v_res_1105_);
return v_r_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg(lean_object* v_a_1107_, lean_object* v_i_1108_, lean_object* v_acc_1109_){
_start:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1110_ = lean_array_get_size(v_a_1107_);
v___x_1111_ = lean_nat_dec_lt(v_i_1108_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_dec(v_i_1108_);
return v_acc_1109_;
}
else
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_array_fget(v_a_1107_, v_i_1108_);
switch(lean_obj_tag(v___x_1112_))
{
case 0:
{
if (lean_obj_tag(v_acc_1109_) == 0)
{
lean_object* v_key_1113_; lean_object* v_val_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1125_; 
v_key_1113_ = lean_ctor_get(v___x_1112_, 0);
v_val_1114_ = lean_ctor_get(v___x_1112_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1116_ = v___x_1112_;
v_isShared_1117_ = v_isSharedCheck_1125_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_val_1114_);
lean_inc(v_key_1113_);
lean_dec(v___x_1112_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1125_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1121_; 
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_nat_add(v_i_1108_, v___x_1118_);
lean_dec(v_i_1108_);
if (v_isShared_1117_ == 0)
{
v___x_1121_ = v___x_1116_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_key_1113_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_val_1114_);
v___x_1121_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1122_; 
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
v_i_1108_ = v___x_1119_;
v_acc_1109_ = v___x_1122_;
goto _start;
}
}
}
else
{
lean_object* v___x_1126_; 
lean_dec_ref_known(v_acc_1109_, 1);
lean_dec_ref_known(v___x_1112_, 2);
lean_dec(v_i_1108_);
v___x_1126_ = lean_box(0);
return v___x_1126_;
}
}
case 1:
{
lean_object* v___x_1127_; 
lean_dec_ref_known(v___x_1112_, 1);
lean_dec(v_acc_1109_);
lean_dec(v_i_1108_);
v___x_1127_ = lean_box(0);
return v___x_1127_;
}
default: 
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_unsigned_to_nat(1u);
v___x_1129_ = lean_nat_add(v_i_1108_, v___x_1128_);
lean_dec(v_i_1108_);
v_i_1108_ = v___x_1129_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg___boxed(lean_object* v_a_1131_, lean_object* v_i_1132_, lean_object* v_acc_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1131_, v_i_1132_, v_acc_1133_);
lean_dec_ref(v_a_1131_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries(lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_a_1137_, lean_object* v_i_1138_, lean_object* v_acc_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1137_, v_i_1138_, v_acc_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___boxed(lean_object* v_00_u03b1_1141_, lean_object* v_00_u03b2_1142_, lean_object* v_a_1143_, lean_object* v_i_1144_, lean_object* v_acc_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_PersistentHashMap_isUnaryEntries(v_00_u03b1_1141_, v_00_u03b2_1142_, v_a_1143_, v_i_1144_, v_acc_1145_);
lean_dec_ref(v_a_1143_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object* v_x_1147_){
_start:
{
if (lean_obj_tag(v_x_1147_) == 0)
{
lean_object* v_es_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v_es_1148_ = lean_ctor_get(v_x_1147_, 0);
lean_inc_ref(v_es_1148_);
lean_dec_ref_known(v_x_1147_, 1);
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = lean_box(0);
v___x_1151_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_es_1148_, v___x_1149_, v___x_1150_);
lean_dec_ref(v_es_1148_);
return v___x_1151_;
}
else
{
lean_object* v_ks_1152_; lean_object* v_vs_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1168_; 
v_ks_1152_ = lean_ctor_get(v_x_1147_, 0);
v_vs_1153_ = lean_ctor_get(v_x_1147_, 1);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_x_1147_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1155_ = v_x_1147_;
v_isShared_1156_ = v_isSharedCheck_1168_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_vs_1153_);
lean_inc(v_ks_1152_);
lean_dec(v_x_1147_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1168_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v___x_1157_ = lean_unsigned_to_nat(1u);
v___x_1158_ = lean_array_get_size(v_ks_1152_);
v___x_1159_ = lean_nat_dec_eq(v___x_1157_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_del_object(v___x_1155_);
lean_dec_ref(v_vs_1153_);
lean_dec_ref(v_ks_1152_);
v___x_1160_ = lean_box(0);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_array_fget(v_ks_1152_, v___x_1161_);
lean_dec_ref(v_ks_1152_);
v___x_1163_ = lean_array_fget(v_vs_1153_, v___x_1161_);
lean_dec_ref(v_vs_1153_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set_tag(v___x_1155_, 0);
lean_ctor_set(v___x_1155_, 1, v___x_1163_);
lean_ctor_set(v___x_1155_, 0, v___x_1162_);
v___x_1165_ = v___x_1155_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode(lean_object* v_00_u03b1_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_x_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg(lean_object* v_inst_1173_, lean_object* v_x_1174_, size_t v_x_1175_, lean_object* v_x_1176_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
lean_object* v_es_1177_; lean_object* v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; lean_object* v_j_1182_; lean_object* v_entry_1183_; 
v_es_1177_ = lean_ctor_get(v_x_1174_, 0);
v___x_1178_ = lean_box(2);
v___x_1179_ = ((size_t)5ULL);
v___x_1180_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_1181_ = lean_usize_land(v_x_1175_, v___x_1180_);
v_j_1182_ = lean_usize_to_nat(v___x_1181_);
v_entry_1183_ = lean_array_get(v___x_1178_, v_es_1177_, v_j_1182_);
switch(lean_obj_tag(v_entry_1183_))
{
case 0:
{
lean_object* v_key_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v_key_1184_ = lean_ctor_get(v_entry_1183_, 0);
lean_inc(v_key_1184_);
lean_dec_ref_known(v_entry_1183_, 2);
v___x_1185_ = lean_apply_2(v_inst_1173_, v_x_1176_, v_key_1184_);
v___x_1186_ = lean_unbox(v___x_1185_);
if (v___x_1186_ == 0)
{
lean_dec(v_j_1182_);
return v_x_1174_;
}
else
{
lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1194_; 
lean_inc_ref(v_es_1177_);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v_x_1174_, 0);
lean_dec(v_unused_1195_);
v___x_1188_ = v_x_1174_;
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
else
{
lean_dec(v_x_1174_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1194_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = lean_array_set(v_es_1177_, v_j_1182_, v___x_1178_);
lean_dec(v_j_1182_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
case 1:
{
lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1229_; 
lean_inc_ref(v_es_1177_);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v_x_1174_, 0);
lean_dec(v_unused_1230_);
v___x_1197_ = v_x_1174_;
v_isShared_1198_ = v_isSharedCheck_1229_;
goto v_resetjp_1196_;
}
else
{
lean_dec(v_x_1174_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1229_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v_node_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1228_; 
v_node_1199_ = lean_ctor_get(v_entry_1183_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_entry_1183_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1201_ = v_entry_1183_;
v_isShared_1202_ = v_isSharedCheck_1228_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_node_1199_);
lean_dec(v_entry_1183_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1228_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_entries_1203_; size_t v___x_1204_; lean_object* v_newNode_1205_; lean_object* v___x_1206_; 
v_entries_1203_ = lean_array_set(v_es_1177_, v_j_1182_, v___x_1178_);
v___x_1204_ = lean_usize_shift_right(v_x_1175_, v___x_1179_);
v_newNode_1205_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1173_, v_node_1199_, v___x_1204_, v_x_1176_);
lean_inc_ref(v_newNode_1205_);
v___x_1206_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1208_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v_newNode_1205_);
v___x_1208_ = v___x_1201_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_newNode_1205_);
v___x_1208_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_array_set(v_entries_1203_, v_j_1182_, v___x_1208_);
lean_dec(v_j_1182_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1209_);
v___x_1211_ = v___x_1197_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
lean_object* v_val_1214_; lean_object* v_fst_1215_; lean_object* v_snd_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v_newNode_1205_);
lean_del_object(v___x_1201_);
v_val_1214_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_val_1214_);
lean_dec_ref_known(v___x_1206_, 1);
v_fst_1215_ = lean_ctor_get(v_val_1214_, 0);
v_snd_1216_ = lean_ctor_get(v_val_1214_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_val_1214_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1218_ = v_val_1214_;
v_isShared_1219_ = v_isSharedCheck_1227_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_snd_1216_);
lean_inc(v_fst_1215_);
lean_dec(v_val_1214_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1227_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_fst_1215_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_snd_1216_);
v___x_1221_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_array_set(v_entries_1203_, v_j_1182_, v___x_1221_);
lean_dec(v_j_1182_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1222_);
v___x_1224_ = v___x_1197_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1182_);
lean_dec(v_x_1176_);
lean_dec_ref(v_inst_1173_);
return v_x_1174_;
}
}
}
else
{
lean_object* v_ks_1231_; lean_object* v_vs_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1246_; 
v_ks_1231_ = lean_ctor_get(v_x_1174_, 0);
v_vs_1232_ = lean_ctor_get(v_x_1174_, 1);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1174_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1234_ = v_x_1174_;
v_isShared_1235_ = v_isSharedCheck_1246_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_vs_1232_);
lean_inc(v_ks_1231_);
lean_dec(v_x_1174_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1246_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Array_finIdxOf_x3f___redArg(v_inst_1173_, v_ks_1231_, v_x_1176_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1238_; 
if (v_isShared_1235_ == 0)
{
v___x_1238_ = v___x_1234_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_ks_1231_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_vs_1232_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
else
{
lean_object* v_val_1240_; lean_object* v_keys_x27_1241_; lean_object* v_vals_x27_1242_; lean_object* v___x_1244_; 
v_val_1240_ = lean_ctor_get(v___x_1236_, 0);
lean_inc_n(v_val_1240_, 2);
lean_dec_ref_known(v___x_1236_, 1);
v_keys_x27_1241_ = l_Array_eraseIdx___redArg(v_ks_1231_, v_val_1240_);
v_vals_x27_1242_ = l_Array_eraseIdx___redArg(v_vs_1232_, v_val_1240_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v_vals_x27_1242_);
lean_ctor_set(v___x_1234_, 0, v_keys_x27_1241_);
v___x_1244_ = v___x_1234_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_keys_x27_1241_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_vals_x27_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg___boxed(lean_object* v_inst_1247_, lean_object* v_x_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
size_t v_x_232__boxed_1251_; lean_object* v_res_1252_; 
v_x_232__boxed_1251_ = lean_unbox_usize(v_x_1249_);
lean_dec(v_x_1249_);
v_res_1252_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1247_, v_x_1248_, v_x_232__boxed_1251_, v_x_1250_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux(lean_object* v_00_u03b1_1253_, lean_object* v_00_u03b2_1254_, lean_object* v_inst_1255_, lean_object* v_x_1256_, size_t v_x_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1255_, v_x_1256_, v_x_1257_, v_x_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___boxed(lean_object* v_00_u03b1_1260_, lean_object* v_00_u03b2_1261_, lean_object* v_inst_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_x_1265_){
_start:
{
size_t v_x_375__boxed_1266_; lean_object* v_res_1267_; 
v_x_375__boxed_1266_ = lean_unbox_usize(v_x_1264_);
lean_dec(v_x_1264_);
v_res_1267_ = l_Lean_PersistentHashMap_eraseAux(v_00_u03b1_1260_, v_00_u03b2_1261_, v_inst_1262_, v_x_1263_, v_x_375__boxed_1266_, v_x_1265_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object* v_x_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_){
_start:
{
lean_object* v___x_1272_; uint64_t v___x_1273_; size_t v_h_1274_; lean_object* v___x_1275_; 
lean_inc(v_x_1271_);
v___x_1272_ = lean_apply_1(v_x_1269_, v_x_1271_);
v___x_1273_ = lean_unbox_uint64(v___x_1272_);
lean_dec_ref(v___x_1272_);
v_h_1274_ = lean_uint64_to_usize(v___x_1273_);
v___x_1275_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_x_1268_, v_x_1270_, v_h_1274_, v_x_1271_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase(lean_object* v_00_u03b1_1276_, lean_object* v_00_u03b2_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_PersistentHashMap_erase___redArg(v_x_1278_, v_x_1279_, v_x_1280_, v_x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg(lean_object* v_inst_1283_, lean_object* v_inst_1284_, lean_object* v_f_1285_, lean_object* v_x_1286_, size_t v_x_1287_, size_t v_x_1288_, lean_object* v_x_1289_){
_start:
{
if (lean_obj_tag(v_x_1286_) == 0)
{
lean_object* v_es_1290_; size_t v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v_j_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v_es_1290_ = lean_ctor_get(v_x_1286_, 0);
v___x_1291_ = ((size_t)5ULL);
v___x_1292_ = ((size_t)1ULL);
v___x_1293_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_1294_ = lean_usize_land(v_x_1287_, v___x_1293_);
v_j_1295_ = lean_usize_to_nat(v___x_1294_);
v___x_1296_ = lean_array_get_size(v_es_1290_);
v___x_1297_ = lean_nat_dec_lt(v_j_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_dec(v_j_1295_);
lean_dec(v_x_1289_);
lean_dec_ref(v_f_1285_);
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
return v_x_1286_;
}
else
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1364_; 
lean_inc_ref(v_es_1290_);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_x_1286_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; 
v_unused_1365_ = lean_ctor_get(v_x_1286_, 0);
lean_dec(v_unused_1365_);
v___x_1299_ = v_x_1286_;
v_isShared_1300_ = v_isSharedCheck_1364_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v_x_1286_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1364_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v_v_1301_; lean_object* v___x_1302_; lean_object* v_xs_x27_1303_; lean_object* v___y_1305_; 
v_v_1301_ = lean_array_fget(v_es_1290_, v_j_1295_);
v___x_1302_ = lean_box(0);
v_xs_x27_1303_ = lean_array_fset(v_es_1290_, v_j_1295_, v___x_1302_);
switch(lean_obj_tag(v_v_1301_))
{
case 0:
{
lean_object* v_key_1310_; lean_object* v_val_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
lean_dec_ref(v_inst_1284_);
v_key_1310_ = lean_ctor_get(v_v_1301_, 0);
v_val_1311_ = lean_ctor_get(v_v_1301_, 1);
lean_inc(v_key_1310_);
lean_inc(v_x_1289_);
v___x_1312_ = lean_apply_2(v_inst_1283_, v_x_1289_, v_key_1310_);
v___x_1313_ = lean_unbox(v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = lean_box(0);
v___x_1315_ = lean_apply_1(v_f_1285_, v___x_1314_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_dec(v_x_1289_);
v___y_1305_ = v_v_1301_;
goto v___jp_1304_;
}
else
{
lean_object* v_val_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
lean_inc(v_val_1311_);
lean_inc(v_key_1310_);
lean_dec_ref_known(v_v_1301_, 2);
v_val_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_val_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1310_, v_val_1311_, v_x_1289_, v_val_1316_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
v___y_1305_ = v___x_1322_;
goto v___jp_1304_;
}
}
}
}
else
{
lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1335_; 
lean_inc(v_val_1311_);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_v_1301_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; lean_object* v_unused_1337_; 
v_unused_1336_ = lean_ctor_get(v_v_1301_, 1);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_v_1301_, 0);
lean_dec(v_unused_1337_);
v___x_1326_ = v_v_1301_;
v_isShared_1327_ = v_isSharedCheck_1335_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v_v_1301_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1335_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_val_1311_);
v___x_1329_ = lean_apply_1(v_f_1285_, v___x_1328_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v___x_1330_; 
lean_del_object(v___x_1326_);
lean_dec(v_x_1289_);
v___x_1330_ = lean_box(2);
v___y_1305_ = v___x_1330_;
goto v___jp_1304_;
}
else
{
lean_object* v_val_1331_; lean_object* v___x_1333_; 
v_val_1331_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v___x_1329_, 1);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 1, v_val_1331_);
lean_ctor_set(v___x_1326_, 0, v_x_1289_);
v___x_1333_ = v___x_1326_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_x_1289_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_val_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
v___y_1305_ = v___x_1333_;
goto v___jp_1304_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1359_; 
v_node_1338_ = lean_ctor_get(v_v_1301_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_v_1301_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1340_ = v_v_1301_;
v_isShared_1341_ = v_isSharedCheck_1359_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_node_1338_);
lean_dec(v_v_1301_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1359_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
size_t v___x_1342_; size_t v___x_1343_; lean_object* v_newNode_1344_; lean_object* v___x_1345_; 
v___x_1342_ = lean_usize_shift_right(v_x_1287_, v___x_1291_);
v___x_1343_ = lean_usize_add(v_x_1288_, v___x_1292_);
v_newNode_1344_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1283_, v_inst_1284_, v_f_1285_, v_node_1338_, v___x_1342_, v___x_1343_, v_x_1289_);
lean_inc_ref(v_newNode_1344_);
v___x_1345_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1344_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v___x_1347_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v_newNode_1344_);
v___x_1347_ = v___x_1340_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_newNode_1344_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
v___y_1305_ = v___x_1347_;
goto v___jp_1304_;
}
}
else
{
lean_object* v_val_1349_; lean_object* v_fst_1350_; lean_object* v_snd_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v_newNode_1344_);
lean_del_object(v___x_1340_);
v_val_1349_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_val_1349_);
lean_dec_ref_known(v___x_1345_, 1);
v_fst_1350_ = lean_ctor_get(v_val_1349_, 0);
v_snd_1351_ = lean_ctor_get(v_val_1349_, 1);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_val_1349_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v_val_1349_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_snd_1351_);
lean_inc(v_fst_1350_);
lean_dec(v_val_1349_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_fst_1350_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_snd_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
v___y_1305_ = v___x_1356_;
goto v___jp_1304_;
}
}
}
}
}
default: 
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_apply_1(v_f_1285_, v___x_1360_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_dec(v_x_1289_);
v___y_1305_ = v_v_1301_;
goto v___jp_1304_;
}
else
{
lean_object* v_val_1362_; lean_object* v___x_1363_; 
v_val_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_val_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_x_1289_);
lean_ctor_set(v___x_1363_, 1, v_val_1362_);
v___y_1305_ = v___x_1363_;
goto v___jp_1304_;
}
}
}
v___jp_1304_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = lean_array_fset(v_xs_x27_1303_, v_j_1295_, v___y_1305_);
lean_dec(v_j_1295_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1306_);
v___x_1308_ = v___x_1299_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
}
else
{
lean_object* v_ks_1366_; lean_object* v_vs_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1400_; 
v_ks_1366_ = lean_ctor_get(v_x_1286_, 0);
v_vs_1367_ = lean_ctor_get(v_x_1286_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_x_1286_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1369_ = v_x_1286_;
v_isShared_1370_ = v_isSharedCheck_1400_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_vs_1367_);
lean_inc(v_ks_1366_);
lean_dec(v_x_1286_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1400_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; 
lean_inc(v_x_1289_);
lean_inc_ref(v_inst_1283_);
v___x_1371_ = l_Array_finIdxOf_x3f___redArg(v_inst_1283_, v_ks_1366_, v_x_1289_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v___x_1373_; 
if (v_isShared_1370_ == 0)
{
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_ks_1366_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_vs_1367_);
v___x_1373_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_apply_1(v_f_1285_, v___x_1374_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_dec(v_x_1289_);
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
return v___x_1373_;
}
else
{
lean_object* v_val_1376_; lean_object* v___x_1377_; 
v_val_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_1283_, v_inst_1284_, v___x_1373_, v_x_1287_, v_x_1288_, v_x_1289_, v_val_1376_);
return v___x_1377_;
}
}
}
else
{
lean_object* v_val_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v_inst_1284_);
lean_dec_ref(v_inst_1283_);
v_val_1379_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1381_ = v___x_1371_;
v_isShared_1382_ = v_isSharedCheck_1399_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_val_1379_);
lean_dec(v___x_1371_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1399_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v_v_x27_1383_; lean_object* v_keys_1384_; lean_object* v_vals_1385_; lean_object* v___x_1387_; 
v_v_x27_1383_ = lean_array_fget(v_vs_1367_, v_val_1379_);
lean_inc(v_val_1379_);
v_keys_1384_ = l_Array_eraseIdx___redArg(v_ks_1366_, v_val_1379_);
v_vals_1385_ = l_Array_eraseIdx___redArg(v_vs_1367_, v_val_1379_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v_v_x27_1383_);
v___x_1387_ = v___x_1381_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_v_x27_1383_);
v___x_1387_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_apply_1(v_f_1285_, v___x_1387_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v___x_1390_; 
lean_dec(v_x_1289_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_vals_1385_);
lean_ctor_set(v___x_1369_, 0, v_keys_1384_);
v___x_1390_ = v___x_1369_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_keys_1384_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_vals_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
lean_object* v_val_1392_; lean_object* v_keys_1393_; lean_object* v_vals_1394_; lean_object* v___x_1396_; 
v_val_1392_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_val_1392_);
lean_dec_ref_known(v___x_1388_, 1);
v_keys_1393_ = lean_array_push(v_keys_1384_, v_x_1289_);
v_vals_1394_ = lean_array_push(v_vals_1385_, v_val_1392_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 1, v_vals_1394_);
lean_ctor_set(v___x_1369_, 0, v_keys_1393_);
v___x_1396_ = v___x_1369_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_keys_1393_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_vals_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg___boxed(lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_f_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_, lean_object* v_x_1407_){
_start:
{
size_t v_x_466__boxed_1408_; size_t v_x_467__boxed_1409_; lean_object* v_res_1410_; 
v_x_466__boxed_1408_ = lean_unbox_usize(v_x_1405_);
lean_dec(v_x_1405_);
v_x_467__boxed_1409_ = lean_unbox_usize(v_x_1406_);
lean_dec(v_x_1406_);
v_res_1410_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1401_, v_inst_1402_, v_f_1403_, v_x_1404_, v_x_466__boxed_1408_, v_x_467__boxed_1409_, v_x_1407_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux(lean_object* v_00_u03b1_1411_, lean_object* v_00_u03b2_1412_, lean_object* v_inst_1413_, lean_object* v_inst_1414_, lean_object* v_f_1415_, lean_object* v_x_1416_, size_t v_x_1417_, size_t v_x_1418_, lean_object* v_x_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1413_, v_inst_1414_, v_f_1415_, v_x_1416_, v_x_1417_, v_x_1418_, v_x_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___boxed(lean_object* v_00_u03b1_1421_, lean_object* v_00_u03b2_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_f_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
size_t v_x_689__boxed_1430_; size_t v_x_690__boxed_1431_; lean_object* v_res_1432_; 
v_x_689__boxed_1430_ = lean_unbox_usize(v_x_1427_);
lean_dec(v_x_1427_);
v_x_690__boxed_1431_ = lean_unbox_usize(v_x_1428_);
lean_dec(v_x_1428_);
v_res_1432_ = l_Lean_PersistentHashMap_alterAux(v_00_u03b1_1421_, v_00_u03b2_1422_, v_inst_1423_, v_inst_1424_, v_f_1425_, v_x_1426_, v_x_689__boxed_1430_, v_x_690__boxed_1431_, v_x_1429_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter___redArg(lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_){
_start:
{
lean_object* v___x_1438_; uint64_t v___x_1439_; size_t v_h_1440_; size_t v___x_1441_; lean_object* v___x_1442_; 
lean_inc_ref(v_x_1434_);
lean_inc(v_x_1436_);
v___x_1438_ = lean_apply_1(v_x_1434_, v_x_1436_);
v___x_1439_ = lean_unbox_uint64(v___x_1438_);
lean_dec_ref(v___x_1438_);
v_h_1440_ = lean_uint64_to_usize(v___x_1439_);
v___x_1441_ = ((size_t)1ULL);
v___x_1442_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1433_, v_x_1434_, v_x_1437_, v_x_1435_, v_h_1440_, v___x_1441_, v_x_1436_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter(lean_object* v_00_u03b1_1443_, lean_object* v_00_u03b2_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_, lean_object* v_x_1449_){
_start:
{
lean_object* v___x_1450_; uint64_t v___x_1451_; size_t v_h_1452_; size_t v___x_1453_; lean_object* v___x_1454_; 
lean_inc_ref(v_x_1446_);
lean_inc(v_x_1448_);
v___x_1450_ = lean_apply_1(v_x_1446_, v_x_1448_);
v___x_1451_ = lean_unbox_uint64(v___x_1450_);
lean_dec_ref(v___x_1450_);
v_h_1452_ = lean_uint64_to_usize(v___x_1451_);
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1445_, v_x_1446_, v_x_1449_, v_x_1447_, v_h_1452_, v___x_1453_, v_x_1448_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed(lean_object* v_i_1455_, lean_object* v_inst_1456_, lean_object* v_f_1457_, lean_object* v_keys_1458_, lean_object* v_vals_1459_, lean_object* v_____do__lift_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(v_i_1455_, v_inst_1456_, v_f_1457_, v_keys_1458_, v_vals_1459_, v_____do__lift_1460_);
lean_dec(v_i_1455_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(lean_object* v_inst_1462_, lean_object* v_f_1463_, lean_object* v_keys_1464_, lean_object* v_vals_1465_, lean_object* v_i_1466_, lean_object* v_acc_1467_){
_start:
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = lean_array_get_size(v_keys_1464_);
v___x_1469_ = lean_nat_dec_lt(v_i_1466_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v_toApplicative_1470_; lean_object* v_toPure_1471_; lean_object* v___x_1472_; 
lean_dec(v_i_1466_);
lean_dec_ref(v_vals_1465_);
lean_dec_ref(v_keys_1464_);
lean_dec(v_f_1463_);
v_toApplicative_1470_ = lean_ctor_get(v_inst_1462_, 0);
lean_inc_ref(v_toApplicative_1470_);
lean_dec_ref(v_inst_1462_);
v_toPure_1471_ = lean_ctor_get(v_toApplicative_1470_, 1);
lean_inc(v_toPure_1471_);
lean_dec_ref(v_toApplicative_1470_);
v___x_1472_ = lean_apply_2(v_toPure_1471_, lean_box(0), v_acc_1467_);
return v___x_1472_;
}
else
{
lean_object* v_toBind_1473_; lean_object* v___f_1474_; lean_object* v_k_1475_; lean_object* v_v_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_toBind_1473_ = lean_ctor_get(v_inst_1462_, 1);
lean_inc(v_toBind_1473_);
lean_inc_ref(v_vals_1465_);
lean_inc_ref(v_keys_1464_);
lean_inc(v_f_1463_);
lean_inc(v_i_1466_);
v___f_1474_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1474_, 0, v_i_1466_);
lean_closure_set(v___f_1474_, 1, v_inst_1462_);
lean_closure_set(v___f_1474_, 2, v_f_1463_);
lean_closure_set(v___f_1474_, 3, v_keys_1464_);
lean_closure_set(v___f_1474_, 4, v_vals_1465_);
v_k_1475_ = lean_array_fget(v_keys_1464_, v_i_1466_);
lean_dec_ref(v_keys_1464_);
v_v_1476_ = lean_array_fget(v_vals_1465_, v_i_1466_);
lean_dec(v_i_1466_);
lean_dec_ref(v_vals_1465_);
v___x_1477_ = lean_apply_3(v_f_1463_, v_acc_1467_, v_k_1475_, v_v_1476_);
v___x_1478_ = lean_apply_4(v_toBind_1473_, lean_box(0), lean_box(0), v___x_1477_, v___f_1474_);
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(lean_object* v_i_1479_, lean_object* v_inst_1480_, lean_object* v_f_1481_, lean_object* v_keys_1482_, lean_object* v_vals_1483_, lean_object* v_____do__lift_1484_){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1485_ = lean_unsigned_to_nat(1u);
v___x_1486_ = lean_nat_add(v_i_1479_, v___x_1485_);
v___x_1487_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1480_, v_f_1481_, v_keys_1482_, v_vals_1483_, v___x_1486_, v_____do__lift_1484_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse(lean_object* v_m_1488_, lean_object* v_inst_1489_, lean_object* v_00_u03c3_1490_, lean_object* v_00_u03b1_1491_, lean_object* v_00_u03b2_1492_, lean_object* v_f_1493_, lean_object* v_keys_1494_, lean_object* v_vals_1495_, lean_object* v_heq_1496_, lean_object* v_i_1497_, lean_object* v_acc_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1489_, v_f_1493_, v_keys_1494_, v_vals_1495_, v_i_1497_, v_acc_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object* v_inst_1500_, lean_object* v_f_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_){
_start:
{
if (lean_obj_tag(v_x_1502_) == 0)
{
lean_object* v_toApplicative_1504_; lean_object* v_toPure_1505_; lean_object* v_es_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v_toApplicative_1504_ = lean_ctor_get(v_inst_1500_, 0);
v_toPure_1505_ = lean_ctor_get(v_toApplicative_1504_, 1);
v_es_1506_ = lean_ctor_get(v_x_1502_, 0);
lean_inc_ref(v_es_1506_);
lean_dec_ref_known(v_x_1502_, 1);
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = lean_array_get_size(v_es_1506_);
v___x_1509_ = lean_nat_dec_lt(v___x_1507_, v___x_1508_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_inc(v_toPure_1505_);
lean_dec_ref(v_es_1506_);
lean_dec(v_f_1501_);
lean_dec_ref(v_inst_1500_);
v___x_1510_ = lean_apply_2(v_toPure_1505_, lean_box(0), v_x_1503_);
return v___x_1510_;
}
else
{
lean_object* v___f_1511_; uint8_t v___x_1512_; 
lean_inc(v_toPure_1505_);
lean_inc_ref(v_inst_1500_);
v___f_1511_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1511_, 0, v_f_1501_);
lean_closure_set(v___f_1511_, 1, v_inst_1500_);
lean_closure_set(v___f_1511_, 2, v_toPure_1505_);
v___x_1512_ = lean_nat_dec_le(v___x_1508_, v___x_1508_);
if (v___x_1512_ == 0)
{
if (v___x_1509_ == 0)
{
lean_object* v___x_1513_; 
lean_inc(v_toPure_1505_);
lean_dec_ref(v___f_1511_);
lean_dec_ref(v_es_1506_);
lean_dec_ref(v_inst_1500_);
v___x_1513_ = lean_apply_2(v_toPure_1505_, lean_box(0), v_x_1503_);
return v___x_1513_;
}
else
{
size_t v___x_1514_; size_t v___x_1515_; lean_object* v___x_1516_; 
v___x_1514_ = ((size_t)0ULL);
v___x_1515_ = lean_usize_of_nat(v___x_1508_);
v___x_1516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1500_, v___f_1511_, v_es_1506_, v___x_1514_, v___x_1515_, v_x_1503_);
return v___x_1516_;
}
}
else
{
size_t v___x_1517_; size_t v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = ((size_t)0ULL);
v___x_1518_ = lean_usize_of_nat(v___x_1508_);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1500_, v___f_1511_, v_es_1506_, v___x_1517_, v___x_1518_, v_x_1503_);
return v___x_1519_;
}
}
}
else
{
lean_object* v_ks_1520_; lean_object* v_vs_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_ks_1520_ = lean_ctor_get(v_x_1502_, 0);
lean_inc_ref(v_ks_1520_);
v_vs_1521_ = lean_ctor_get(v_x_1502_, 1);
lean_inc_ref(v_vs_1521_);
lean_dec_ref_known(v_x_1502_, 2);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1500_, v_f_1501_, v_ks_1520_, v_vs_1521_, v___x_1522_, v_x_1503_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0(lean_object* v_f_1524_, lean_object* v_inst_1525_, lean_object* v_toPure_1526_, lean_object* v_acc_1527_, lean_object* v_entry_1528_){
_start:
{
switch(lean_obj_tag(v_entry_1528_))
{
case 0:
{
lean_object* v_key_1529_; lean_object* v_val_1530_; lean_object* v___x_1531_; 
lean_dec(v_toPure_1526_);
lean_dec_ref(v_inst_1525_);
v_key_1529_ = lean_ctor_get(v_entry_1528_, 0);
lean_inc(v_key_1529_);
v_val_1530_ = lean_ctor_get(v_entry_1528_, 1);
lean_inc(v_val_1530_);
lean_dec_ref_known(v_entry_1528_, 2);
v___x_1531_ = lean_apply_3(v_f_1524_, v_acc_1527_, v_key_1529_, v_val_1530_);
return v___x_1531_;
}
case 1:
{
lean_object* v_node_1532_; lean_object* v___x_1533_; 
lean_dec(v_toPure_1526_);
v_node_1532_ = lean_ctor_get(v_entry_1528_, 0);
lean_inc(v_node_1532_);
lean_dec_ref_known(v_entry_1528_, 1);
v___x_1533_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1525_, v_f_1524_, v_node_1532_, v_acc_1527_);
return v___x_1533_;
}
default: 
{
lean_object* v___x_1534_; 
lean_dec_ref(v_inst_1525_);
lean_dec(v_f_1524_);
v___x_1534_ = lean_apply_2(v_toPure_1526_, lean_box(0), v_acc_1527_);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux(lean_object* v_m_1535_, lean_object* v_inst_1536_, lean_object* v_00_u03c3_1537_, lean_object* v_00_u03b1_1538_, lean_object* v_00_u03b2_1539_, lean_object* v_f_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1536_, v_f_1540_, v_x_1541_, v_x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___redArg(lean_object* v_inst_1544_, lean_object* v_map_1545_, lean_object* v_f_1546_, lean_object* v_init_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1544_, v_f_1546_, v_map_1545_, v_init_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM(lean_object* v_m_1549_, lean_object* v_inst_1550_, lean_object* v_00_u03c3_1551_, lean_object* v_00_u03b1_1552_, lean_object* v_00_u03b2_1553_, lean_object* v_x_1554_, lean_object* v_x_1555_, lean_object* v_map_1556_, lean_object* v_f_1557_, lean_object* v_init_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1550_, v_f_1557_, v_map_1556_, v_init_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___boxed(lean_object* v_m_1560_, lean_object* v_inst_1561_, lean_object* v_00_u03c3_1562_, lean_object* v_00_u03b1_1563_, lean_object* v_00_u03b2_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v_map_1567_, lean_object* v_f_1568_, lean_object* v_init_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_PersistentHashMap_foldlM(v_m_1560_, v_inst_1561_, v_00_u03c3_1562_, v_00_u03b1_1563_, v_00_u03b2_1564_, v_x_1565_, v_x_1566_, v_map_1567_, v_f_1568_, v_init_1569_);
lean_dec_ref(v_x_1566_);
lean_dec_ref(v_x_1565_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg___lam__0(lean_object* v_f_1571_, lean_object* v_x_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_apply_2(v_f_1571_, v___y_1573_, v___y_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg(lean_object* v_inst_1576_, lean_object* v_map_1577_, lean_object* v_f_1578_){
_start:
{
lean_object* v___f_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___f_1579_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1579_, 0, v_f_1578_);
v___x_1580_ = lean_box(0);
v___x_1581_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1576_, v___f_1579_, v_map_1577_, v___x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM(lean_object* v_m_1582_, lean_object* v_inst_1583_, lean_object* v_00_u03b1_1584_, lean_object* v_00_u03b2_1585_, lean_object* v_x_1586_, lean_object* v_x_1587_, lean_object* v_map_1588_, lean_object* v_f_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_1583_, v_map_1588_, v_f_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___boxed(lean_object* v_m_1591_, lean_object* v_inst_1592_, lean_object* v_00_u03b1_1593_, lean_object* v_00_u03b2_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_, lean_object* v_map_1597_, lean_object* v_f_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_PersistentHashMap_forM(v_m_1591_, v_inst_1592_, v_00_u03b1_1593_, v_00_u03b2_1594_, v_x_1595_, v_x_1596_, v_map_1597_, v_f_1598_);
lean_dec_ref(v_x_1596_);
lean_dec_ref(v_x_1595_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg___lam__0(lean_object* v_f_1600_, lean_object* v_x1_1601_, lean_object* v_x2_1602_, lean_object* v_x3_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_apply_3(v_f_1600_, v_x1_1601_, v_x2_1602_, v_x3_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object* v_map_1624_, lean_object* v_f_1625_, lean_object* v_init_1626_){
_start:
{
lean_object* v___f_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___f_1627_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1627_, 0, v_f_1625_);
v___x_1628_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1629_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1628_, v___f_1627_, v_map_1624_, v_init_1626_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl(lean_object* v_00_u03c3_1630_, lean_object* v_00_u03b1_1631_, lean_object* v_00_u03b2_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_, lean_object* v_map_1635_, lean_object* v_f_1636_, lean_object* v_init_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_1635_, v_f_1636_, v_init_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___boxed(lean_object* v_00_u03c3_1639_, lean_object* v_00_u03b1_1640_, lean_object* v_00_u03b2_1641_, lean_object* v_x_1642_, lean_object* v_x_1643_, lean_object* v_map_1644_, lean_object* v_f_1645_, lean_object* v_init_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_Lean_PersistentHashMap_foldl(v_00_u03c3_1639_, v_00_u03b1_1640_, v_00_u03b2_1641_, v_x_1642_, v_x_1643_, v_map_1644_, v_f_1645_, v_init_1646_);
lean_dec_ref(v_x_1643_);
lean_dec_ref(v_x_1642_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__0(lean_object* v_x_1648_){
_start:
{
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_a_1649_ = lean_ctor_get(v_x_1648_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_x_1648_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1651_ = v_x_1648_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_a_1649_);
lean_dec(v_x_1648_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_a_1657_ = lean_ctor_get(v_x_1648_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_x_1648_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v_x_1648_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v_x_1648_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__1(lean_object* v_toPure_1665_, lean_object* v_result_1666_){
_start:
{
lean_object* v_a_1667_; lean_object* v___x_1668_; 
v_a_1667_ = lean_ctor_get(v_result_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref(v_result_1666_);
v___x_1668_ = lean_apply_2(v_toPure_1665_, lean_box(0), v_a_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__2(lean_object* v_toFunctor_1669_, lean_object* v_f_1670_, lean_object* v_intoError_1671_, lean_object* v_s_1672_, lean_object* v_a_1673_, lean_object* v_b_1674_){
_start:
{
lean_object* v_map_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1684_; 
v_map_1675_ = lean_ctor_get(v_toFunctor_1669_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_toFunctor_1669_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v_toFunctor_1669_, 1);
lean_dec(v_unused_1685_);
v___x_1677_ = v_toFunctor_1669_;
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_map_1675_);
lean_dec(v_toFunctor_1669_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1684_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v_b_1674_);
lean_ctor_set(v___x_1677_, 0, v_a_1673_);
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1673_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_b_1674_);
v___x_1680_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_apply_2(v_f_1670_, v___x_1680_, v_s_1672_);
v___x_1682_ = lean_apply_4(v_map_1675_, lean_box(0), lean_box(0), v_intoError_1671_, v___x_1681_);
return v___x_1682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg(lean_object* v_inst_1687_, lean_object* v_map_1688_, lean_object* v_init_1689_, lean_object* v_f_1690_){
_start:
{
lean_object* v_toApplicative_1691_; lean_object* v_toBind_1692_; lean_object* v___f_1693_; lean_object* v___f_1694_; lean_object* v___f_1695_; lean_object* v___f_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v_toFunctor_1703_; lean_object* v_toPure_1704_; lean_object* v_intoError_1705_; lean_object* v___f_1706_; lean_object* v___f_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v_toApplicative_1691_ = lean_ctor_get(v_inst_1687_, 0);
lean_inc_ref(v_toApplicative_1691_);
v_toBind_1692_ = lean_ctor_get(v_inst_1687_, 1);
lean_inc(v_toBind_1692_);
lean_inc_ref_n(v_inst_1687_, 6);
v___f_1693_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1693_, 0, v_inst_1687_);
v___f_1694_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1694_, 0, v_inst_1687_);
v___f_1695_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1695_, 0, v_inst_1687_);
v___f_1696_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1696_, 0, v_inst_1687_);
v___x_1697_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1697_, 0, lean_box(0));
lean_closure_set(v___x_1697_, 1, lean_box(0));
lean_closure_set(v___x_1697_, 2, v_inst_1687_);
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
lean_ctor_set(v___x_1698_, 1, v___f_1693_);
v___x_1699_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1699_, 0, lean_box(0));
lean_closure_set(v___x_1699_, 1, lean_box(0));
lean_closure_set(v___x_1699_, 2, v_inst_1687_);
v___x_1700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
lean_ctor_set(v___x_1700_, 2, v___f_1694_);
lean_ctor_set(v___x_1700_, 3, v___f_1695_);
lean_ctor_set(v___x_1700_, 4, v___f_1696_);
v___x_1701_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1701_, 0, lean_box(0));
lean_closure_set(v___x_1701_, 1, lean_box(0));
lean_closure_set(v___x_1701_, 2, v_inst_1687_);
v___x_1702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1700_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
v_toFunctor_1703_ = lean_ctor_get(v_toApplicative_1691_, 0);
lean_inc_ref(v_toFunctor_1703_);
v_toPure_1704_ = lean_ctor_get(v_toApplicative_1691_, 1);
lean_inc(v_toPure_1704_);
lean_dec_ref(v_toApplicative_1691_);
v_intoError_1705_ = ((lean_object*)(l_Lean_PersistentHashMap_forIn___redArg___closed__0));
v___f_1706_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1706_, 0, v_toPure_1704_);
v___f_1707_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__2), 6, 3);
lean_closure_set(v___f_1707_, 0, v_toFunctor_1703_);
lean_closure_set(v___f_1707_, 1, v_f_1690_);
lean_closure_set(v___f_1707_, 2, v_intoError_1705_);
lean_inc_ref(v_map_1688_);
v___x_1708_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1702_, v___f_1707_, v_map_1688_, v_init_1689_);
v___x_1709_ = lean_apply_4(v_toBind_1692_, lean_box(0), lean_box(0), v___x_1708_, v___f_1706_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___boxed(lean_object* v_inst_1710_, lean_object* v_map_1711_, lean_object* v_init_1712_, lean_object* v_f_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1710_, v_map_1711_, v_init_1712_, v_f_1713_);
lean_dec_ref(v_map_1711_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn(lean_object* v_m_1715_, lean_object* v_00_u03c3_1716_, lean_object* v_00_u03b1_1717_, lean_object* v_00_u03b2_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_, lean_object* v_inst_1721_, lean_object* v_map_1722_, lean_object* v_init_1723_, lean_object* v_f_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1721_, v_map_1722_, v_init_1723_, v_f_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___boxed(lean_object* v_m_1726_, lean_object* v_00_u03c3_1727_, lean_object* v_00_u03b1_1728_, lean_object* v_00_u03b2_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_inst_1732_, lean_object* v_map_1733_, lean_object* v_init_1734_, lean_object* v_f_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_PersistentHashMap_forIn(v_m_1726_, v_00_u03c3_1727_, v_00_u03b1_1728_, v_00_u03b2_1729_, v_x_1730_, v_x_1731_, v_inst_1732_, v_map_1733_, v_init_1734_, v_f_1735_);
lean_dec_ref(v_map_1733_);
lean_dec_ref(v_x_1731_);
lean_dec_ref(v_x_1730_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_inst_1737_, lean_object* v_00_u03b2_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1737_, v___y_1739_, v___y_1740_, v___y_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed(lean_object* v_inst_1743_, lean_object* v_00_u03b2_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(v_inst_1743_, v_00_u03b2_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec_ref(v___y_1745_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1749_){
_start:
{
lean_object* v___f_1750_; 
v___f_1750_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1750_, 0, v_inst_1749_);
return v___f_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad(lean_object* v_m_1751_, lean_object* v_00_u03b1_1752_, lean_object* v_00_u03b2_1753_, lean_object* v_x_1754_, lean_object* v_x_1755_, lean_object* v_inst_1756_){
_start:
{
lean_object* v___f_1757_; 
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1757_, 0, v_inst_1756_);
return v___f_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___boxed(lean_object* v_m_1758_, lean_object* v_00_u03b1_1759_, lean_object* v_00_u03b2_1760_, lean_object* v_x_1761_, lean_object* v_x_1762_, lean_object* v_inst_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_PersistentHashMap_instForInProdOfMonad(v_m_1758_, v_00_u03b1_1759_, v_00_u03b2_1760_, v_x_1761_, v_x_1762_, v_inst_1763_);
lean_dec_ref(v_x_1762_);
lean_dec_ref(v_x_1761_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__0(lean_object* v_toPure_1765_, lean_object* v_entries_x27_1766_){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_entries_x27_1766_);
v___x_1768_ = lean_apply_2(v_toPure_1765_, lean_box(0), v___x_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__1(lean_object* v_toPure_1769_, lean_object* v_____do__lift_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_____do__lift_1770_);
v___x_1772_ = lean_apply_2(v_toPure_1769_, lean_box(0), v___x_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__2(lean_object* v_key_1773_, lean_object* v_toPure_1774_, lean_object* v_____do__lift_1775_){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v_key_1773_);
lean_ctor_set(v___x_1776_, 1, v_____do__lift_1775_);
v___x_1777_ = lean_apply_2(v_toPure_1774_, lean_box(0), v___x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__4(lean_object* v_ks_1778_, lean_object* v_toPure_1779_, lean_object* v_____x_1780_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1781_, 0, v_ks_1778_);
lean_ctor_set(v___x_1781_, 1, v_____x_1780_);
v___x_1782_ = lean_apply_2(v_toPure_1779_, lean_box(0), v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg(lean_object* v_inst_1783_, lean_object* v_f_1784_, lean_object* v_n_1785_){
_start:
{
if (lean_obj_tag(v_n_1785_) == 0)
{
lean_object* v_toApplicative_1786_; lean_object* v_toBind_1787_; lean_object* v_toPure_1788_; lean_object* v_es_1789_; lean_object* v___f_1790_; lean_object* v___f_1791_; lean_object* v___f_1792_; size_t v_sz_1793_; size_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_toApplicative_1786_ = lean_ctor_get(v_inst_1783_, 0);
v_toBind_1787_ = lean_ctor_get(v_inst_1783_, 1);
lean_inc_n(v_toBind_1787_, 2);
v_toPure_1788_ = lean_ctor_get(v_toApplicative_1786_, 1);
v_es_1789_ = lean_ctor_get(v_n_1785_, 0);
lean_inc_ref(v_es_1789_);
lean_dec_ref_known(v_n_1785_, 1);
lean_inc_n(v_toPure_1788_, 3);
v___f_1790_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1790_, 0, v_toPure_1788_);
v___f_1791_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1791_, 0, v_toPure_1788_);
lean_inc_ref(v_inst_1783_);
v___f_1792_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1792_, 0, v_toPure_1788_);
lean_closure_set(v___f_1792_, 1, v_f_1784_);
lean_closure_set(v___f_1792_, 2, v_toBind_1787_);
lean_closure_set(v___f_1792_, 3, v_inst_1783_);
lean_closure_set(v___f_1792_, 4, v___f_1791_);
v_sz_1793_ = lean_array_size(v_es_1789_);
v___x_1794_ = ((size_t)0ULL);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1783_, v___f_1792_, v_sz_1793_, v___x_1794_, v_es_1789_);
v___x_1796_ = lean_apply_4(v_toBind_1787_, lean_box(0), lean_box(0), v___x_1795_, v___f_1790_);
return v___x_1796_;
}
else
{
lean_object* v_toApplicative_1797_; lean_object* v_toBind_1798_; lean_object* v_toPure_1799_; lean_object* v_ks_1800_; lean_object* v_vs_1801_; lean_object* v___f_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_toApplicative_1797_ = lean_ctor_get(v_inst_1783_, 0);
v_toBind_1798_ = lean_ctor_get(v_inst_1783_, 1);
lean_inc(v_toBind_1798_);
v_toPure_1799_ = lean_ctor_get(v_toApplicative_1797_, 1);
v_ks_1800_ = lean_ctor_get(v_n_1785_, 0);
lean_inc_ref(v_ks_1800_);
v_vs_1801_ = lean_ctor_get(v_n_1785_, 1);
lean_inc_ref(v_vs_1801_);
lean_dec_ref_known(v_n_1785_, 2);
lean_inc(v_toPure_1799_);
v___f_1802_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__4), 3, 2);
lean_closure_set(v___f_1802_, 0, v_ks_1800_);
lean_closure_set(v___f_1802_, 1, v_toPure_1799_);
v___x_1803_ = l_Array_mapM_x27___redArg(v_inst_1783_, v_f_1784_, v_vs_1801_);
v___x_1804_ = lean_apply_4(v_toBind_1798_, lean_box(0), lean_box(0), v___x_1803_, v___f_1802_);
return v___x_1804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__3(lean_object* v_toPure_1805_, lean_object* v_f_1806_, lean_object* v_toBind_1807_, lean_object* v_inst_1808_, lean_object* v___f_1809_, lean_object* v_x_1810_){
_start:
{
switch(lean_obj_tag(v_x_1810_))
{
case 0:
{
lean_object* v_key_1811_; lean_object* v_val_1812_; lean_object* v___f_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
lean_dec(v___f_1809_);
lean_dec_ref(v_inst_1808_);
v_key_1811_ = lean_ctor_get(v_x_1810_, 0);
lean_inc(v_key_1811_);
v_val_1812_ = lean_ctor_get(v_x_1810_, 1);
lean_inc(v_val_1812_);
lean_dec_ref_known(v_x_1810_, 2);
v___f_1813_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1813_, 0, v_key_1811_);
lean_closure_set(v___f_1813_, 1, v_toPure_1805_);
v___x_1814_ = lean_apply_1(v_f_1806_, v_val_1812_);
v___x_1815_ = lean_apply_4(v_toBind_1807_, lean_box(0), lean_box(0), v___x_1814_, v___f_1813_);
return v___x_1815_;
}
case 1:
{
lean_object* v_node_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
lean_dec(v_toPure_1805_);
v_node_1816_ = lean_ctor_get(v_x_1810_, 0);
lean_inc(v_node_1816_);
lean_dec_ref_known(v_x_1810_, 1);
v___x_1817_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1808_, v_f_1806_, v_node_1816_);
v___x_1818_ = lean_apply_4(v_toBind_1807_, lean_box(0), lean_box(0), v___x_1817_, v___f_1809_);
return v___x_1818_;
}
default: 
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec(v___f_1809_);
lean_dec_ref(v_inst_1808_);
lean_dec(v_toBind_1807_);
lean_dec(v_f_1806_);
v___x_1819_ = lean_box(2);
v___x_1820_ = lean_apply_2(v_toPure_1805_, lean_box(0), v___x_1819_);
return v___x_1820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux(lean_object* v_00_u03b1_1821_, lean_object* v_00_u03b2_1822_, lean_object* v_00_u03c3_1823_, lean_object* v_m_1824_, lean_object* v_inst_1825_, lean_object* v_f_1826_, lean_object* v_n_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1825_, v_f_1826_, v_n_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg___lam__0(lean_object* v_toPure_1829_, lean_object* v_root_1830_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_apply_2(v_toPure_1829_, lean_box(0), v_root_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object* v_inst_1832_, lean_object* v_pm_1833_, lean_object* v_f_1834_){
_start:
{
lean_object* v_toApplicative_1835_; lean_object* v_toBind_1836_; lean_object* v_toPure_1837_; lean_object* v___x_1838_; lean_object* v___f_1839_; lean_object* v___x_1840_; 
v_toApplicative_1835_ = lean_ctor_get(v_inst_1832_, 0);
v_toBind_1836_ = lean_ctor_get(v_inst_1832_, 1);
lean_inc(v_toBind_1836_);
v_toPure_1837_ = lean_ctor_get(v_toApplicative_1835_, 1);
lean_inc(v_toPure_1837_);
v___x_1838_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1832_, v_f_1834_, v_pm_1833_);
v___f_1839_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1839_, 0, v_toPure_1837_);
v___x_1840_ = lean_apply_4(v_toBind_1836_, lean_box(0), lean_box(0), v___x_1838_, v___f_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM(lean_object* v_00_u03b1_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_00_u03c3_1843_, lean_object* v_m_1844_, lean_object* v_inst_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_pm_1848_, lean_object* v_f_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_1845_, v_pm_1848_, v_f_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___boxed(lean_object* v_00_u03b1_1851_, lean_object* v_00_u03b2_1852_, lean_object* v_00_u03c3_1853_, lean_object* v_m_1854_, lean_object* v_inst_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_, lean_object* v_pm_1858_, lean_object* v_f_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Lean_PersistentHashMap_mapM(v_00_u03b1_1851_, v_00_u03b2_1852_, v_00_u03c3_1853_, v_m_1854_, v_inst_1855_, v_x_1856_, v_x_1857_, v_pm_1858_, v_f_1859_);
lean_dec_ref(v_x_1857_);
lean_dec_ref(v_x_1856_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg___lam__0(lean_object* v_f_1861_, lean_object* v_x_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_apply_1(v_f_1861_, v_x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg(lean_object* v_pm_1864_, lean_object* v_f_1865_){
_start:
{
lean_object* v___f_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___f_1866_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1866_, 0, v_f_1865_);
v___x_1867_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1868_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_1867_, v_pm_1864_, v___f_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map(lean_object* v_00_u03b1_1869_, lean_object* v_00_u03b2_1870_, lean_object* v_00_u03c3_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_, lean_object* v_pm_1874_, lean_object* v_f_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_PersistentHashMap_map___redArg(v_pm_1874_, v_f_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___boxed(lean_object* v_00_u03b1_1877_, lean_object* v_00_u03b2_1878_, lean_object* v_00_u03c3_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v_pm_1882_, lean_object* v_f_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_PersistentHashMap_map(v_00_u03b1_1877_, v_00_u03b2_1878_, v_00_u03c3_1879_, v_x_1880_, v_x_1881_, v_pm_1882_, v_f_1883_);
lean_dec_ref(v_x_1881_);
lean_dec_ref(v_x_1880_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg___lam__0(lean_object* v_ps_1885_, lean_object* v_k_1886_, lean_object* v_v_1887_){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v_k_1886_);
lean_ctor_set(v___x_1888_, 1, v_v_1887_);
v___x_1889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
lean_ctor_set(v___x_1889_, 1, v_ps_1885_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg(lean_object* v_m_1891_){
_start:
{
lean_object* v___f_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___f_1892_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___redArg___closed__0));
v___x_1893_ = lean_box(0);
v___x_1894_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1891_, v___f_1892_, v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList(lean_object* v_00_u03b1_1895_, lean_object* v_00_u03b2_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v_m_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_PersistentHashMap_toList___redArg(v_m_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___boxed(lean_object* v_00_u03b1_1901_, lean_object* v_00_u03b2_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_, lean_object* v_m_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_PersistentHashMap_toList(v_00_u03b1_1901_, v_00_u03b2_1902_, v_x_1903_, v_x_1904_, v_m_1905_);
lean_dec_ref(v_x_1904_);
lean_dec_ref(v_x_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg___lam__0(lean_object* v_ps_1907_, lean_object* v_k_1908_, lean_object* v_v_1909_){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1910_, 0, v_k_1908_);
lean_ctor_set(v___x_1910_, 1, v_v_1909_);
v___x_1911_ = lean_array_push(v_ps_1907_, v___x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg(lean_object* v_m_1915_){
_start:
{
lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___f_1916_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__0));
v___x_1917_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__1));
v___x_1918_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1915_, v___f_1916_, v___x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray(lean_object* v_00_u03b1_1919_, lean_object* v_00_u03b2_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_m_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Lean_PersistentHashMap_toArray___redArg(v_m_1923_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___boxed(lean_object* v_00_u03b1_1925_, lean_object* v_00_u03b2_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_, lean_object* v_m_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_PersistentHashMap_toArray(v_00_u03b1_1925_, v_00_u03b2_1926_, v_x_1927_, v_x_1928_, v_m_1929_);
lean_dec_ref(v_x_1928_);
lean_dec_ref(v_x_1927_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg(lean_object* v_x_1931_, lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
if (lean_obj_tag(v_x_1931_) == 0)
{
lean_object* v_es_1934_; lean_object* v_numNodes_1935_; lean_object* v_numNull_1936_; lean_object* v_numCollisions_1937_; lean_object* v_maxDepth_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1960_; 
v_es_1934_ = lean_ctor_get(v_x_1931_, 0);
v_numNodes_1935_ = lean_ctor_get(v_x_1932_, 0);
v_numNull_1936_ = lean_ctor_get(v_x_1932_, 1);
v_numCollisions_1937_ = lean_ctor_get(v_x_1932_, 2);
v_maxDepth_1938_ = lean_ctor_get(v_x_1932_, 3);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_x_1932_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1940_ = v_x_1932_;
v_isShared_1941_ = v_isSharedCheck_1960_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_maxDepth_1938_);
lean_inc(v_numCollisions_1937_);
lean_inc(v_numNull_1936_);
lean_inc(v_numNodes_1935_);
lean_dec(v_x_1932_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1960_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___y_1945_; uint8_t v___x_1959_; 
v___x_1942_ = lean_unsigned_to_nat(1u);
v___x_1943_ = lean_nat_add(v_numNodes_1935_, v___x_1942_);
lean_dec(v_numNodes_1935_);
v___x_1959_ = lean_nat_dec_le(v_maxDepth_1938_, v_x_1933_);
if (v___x_1959_ == 0)
{
v___y_1945_ = v_maxDepth_1938_;
goto v___jp_1944_;
}
else
{
lean_dec(v_maxDepth_1938_);
lean_inc(v_x_1933_);
v___y_1945_ = v_x_1933_;
goto v___jp_1944_;
}
v___jp_1944_:
{
lean_object* v_stats_1947_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 3, v___y_1945_);
lean_ctor_set(v___x_1940_, 0, v___x_1943_);
v_stats_1947_ = v___x_1940_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v_numNull_1936_);
lean_ctor_set(v_reuseFailAlloc_1958_, 2, v_numCollisions_1937_);
lean_ctor_set(v_reuseFailAlloc_1958_, 3, v___y_1945_);
v_stats_1947_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = lean_array_get_size(v_es_1934_);
v___x_1950_ = lean_nat_dec_lt(v___x_1948_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_dec(v_x_1933_);
return v_stats_1947_;
}
else
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_nat_dec_le(v___x_1949_, v___x_1949_);
if (v___x_1951_ == 0)
{
if (v___x_1950_ == 0)
{
lean_dec(v_x_1933_);
return v_stats_1947_;
}
else
{
size_t v___x_1952_; size_t v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = ((size_t)0ULL);
v___x_1953_ = lean_usize_of_nat(v___x_1949_);
v___x_1954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1933_, v_es_1934_, v___x_1952_, v___x_1953_, v_stats_1947_);
lean_dec(v_x_1933_);
return v___x_1954_;
}
}
else
{
size_t v___x_1955_; size_t v___x_1956_; lean_object* v___x_1957_; 
v___x_1955_ = ((size_t)0ULL);
v___x_1956_ = lean_usize_of_nat(v___x_1949_);
v___x_1957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1933_, v_es_1934_, v___x_1955_, v___x_1956_, v_stats_1947_);
lean_dec(v_x_1933_);
return v___x_1957_;
}
}
}
}
}
}
else
{
lean_object* v_ks_1961_; lean_object* v_numNodes_1962_; lean_object* v_numNull_1963_; lean_object* v_numCollisions_1964_; lean_object* v_maxDepth_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1981_; 
v_ks_1961_ = lean_ctor_get(v_x_1931_, 0);
v_numNodes_1962_ = lean_ctor_get(v_x_1932_, 0);
v_numNull_1963_ = lean_ctor_get(v_x_1932_, 1);
v_numCollisions_1964_ = lean_ctor_get(v_x_1932_, 2);
v_maxDepth_1965_ = lean_ctor_get(v_x_1932_, 3);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_x_1932_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1967_ = v_x_1932_;
v_isShared_1968_ = v_isSharedCheck_1981_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_maxDepth_1965_);
lean_inc(v_numCollisions_1964_);
lean_inc(v_numNull_1963_);
lean_inc(v_numNodes_1962_);
lean_dec(v_x_1932_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1981_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1969_ = lean_unsigned_to_nat(1u);
v___x_1970_ = lean_nat_add(v_numNodes_1962_, v___x_1969_);
lean_dec(v_numNodes_1962_);
v___x_1971_ = lean_array_get_size(v_ks_1961_);
v___x_1972_ = lean_nat_add(v_numCollisions_1964_, v___x_1971_);
lean_dec(v_numCollisions_1964_);
v___x_1973_ = lean_nat_sub(v___x_1972_, v___x_1969_);
lean_dec(v___x_1972_);
v___x_1974_ = lean_nat_dec_le(v_maxDepth_1965_, v_x_1933_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1976_; 
lean_dec(v_x_1933_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 2, v___x_1973_);
lean_ctor_set(v___x_1967_, 0, v___x_1970_);
v___x_1976_ = v___x_1967_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_numNull_1963_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_maxDepth_1965_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
else
{
lean_object* v___x_1979_; 
lean_dec(v_maxDepth_1965_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 3, v_x_1933_);
lean_ctor_set(v___x_1967_, 2, v___x_1973_);
lean_ctor_set(v___x_1967_, 0, v___x_1970_);
v___x_1979_ = v___x_1967_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1980_, 1, v_numNull_1963_);
lean_ctor_set(v_reuseFailAlloc_1980_, 2, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1980_, 3, v_x_1933_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(lean_object* v_x_1982_, lean_object* v_as_1983_, size_t v_i_1984_, size_t v_stop_1985_, lean_object* v_b_1986_){
_start:
{
lean_object* v___y_1988_; uint8_t v___x_1992_; 
v___x_1992_ = lean_usize_dec_eq(v_i_1984_, v_stop_1985_);
if (v___x_1992_ == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_unsigned_to_nat(1u);
v___x_1994_ = lean_array_uget_borrowed(v_as_1983_, v_i_1984_);
switch(lean_obj_tag(v___x_1994_))
{
case 0:
{
v___y_1988_ = v_b_1986_;
goto v___jp_1987_;
}
case 1:
{
lean_object* v_node_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_node_1995_ = lean_ctor_get(v___x_1994_, 0);
v___x_1996_ = lean_nat_add(v_x_1982_, v___x_1993_);
v___x_1997_ = l_Lean_PersistentHashMap_collectStats___redArg(v_node_1995_, v_b_1986_, v___x_1996_);
v___y_1988_ = v___x_1997_;
goto v___jp_1987_;
}
default: 
{
lean_object* v_numNodes_1998_; lean_object* v_numNull_1999_; lean_object* v_numCollisions_2000_; lean_object* v_maxDepth_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2009_; 
v_numNodes_1998_ = lean_ctor_get(v_b_1986_, 0);
v_numNull_1999_ = lean_ctor_get(v_b_1986_, 1);
v_numCollisions_2000_ = lean_ctor_get(v_b_1986_, 2);
v_maxDepth_2001_ = lean_ctor_get(v_b_1986_, 3);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_b_1986_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2003_ = v_b_1986_;
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_maxDepth_2001_);
lean_inc(v_numCollisions_2000_);
lean_inc(v_numNull_1999_);
lean_inc(v_numNodes_1998_);
lean_dec(v_b_1986_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_nat_add(v_numNull_1999_, v___x_1993_);
lean_dec(v_numNull_1999_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 1, v___x_2005_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_numNodes_1998_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_numCollisions_2000_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_maxDepth_2001_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
v___y_1988_ = v___x_2007_;
goto v___jp_1987_;
}
}
}
}
}
else
{
return v_b_1986_;
}
v___jp_1987_:
{
size_t v___x_1989_; size_t v___x_1990_; 
v___x_1989_ = ((size_t)1ULL);
v___x_1990_ = lean_usize_add(v_i_1984_, v___x_1989_);
v_i_1984_ = v___x_1990_;
v_b_1986_ = v___y_1988_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg___boxed(lean_object* v_x_2010_, lean_object* v_as_2011_, lean_object* v_i_2012_, lean_object* v_stop_2013_, lean_object* v_b_2014_){
_start:
{
size_t v_i_boxed_2015_; size_t v_stop_boxed_2016_; lean_object* v_res_2017_; 
v_i_boxed_2015_ = lean_unbox_usize(v_i_2012_);
lean_dec(v_i_2012_);
v_stop_boxed_2016_ = lean_unbox_usize(v_stop_2013_);
lean_dec(v_stop_2013_);
v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2010_, v_as_2011_, v_i_boxed_2015_, v_stop_boxed_2016_, v_b_2014_);
lean_dec_ref(v_as_2011_);
lean_dec(v_x_2010_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg___boxed(lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2018_, v_x_2019_, v_x_2020_);
lean_dec_ref(v_x_2018_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats(lean_object* v_00_u03b1_2022_, lean_object* v_00_u03b2_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2024_, v_x_2025_, v_x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___boxed(lean_object* v_00_u03b1_2028_, lean_object* v_00_u03b2_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Lean_PersistentHashMap_collectStats(v_00_u03b1_2028_, v_00_u03b2_2029_, v_x_2030_, v_x_2031_, v_x_2032_);
lean_dec_ref(v_x_2030_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(lean_object* v_00_u03b1_2034_, lean_object* v_00_u03b2_2035_, lean_object* v_x_2036_, lean_object* v_as_2037_, size_t v_i_2038_, size_t v_stop_2039_, lean_object* v_b_2040_){
_start:
{
lean_object* v___x_2041_; 
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2036_, v_as_2037_, v_i_2038_, v_stop_2039_, v_b_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2042_, lean_object* v_00_u03b2_2043_, lean_object* v_x_2044_, lean_object* v_as_2045_, lean_object* v_i_2046_, lean_object* v_stop_2047_, lean_object* v_b_2048_){
_start:
{
size_t v_i_boxed_2049_; size_t v_stop_boxed_2050_; lean_object* v_res_2051_; 
v_i_boxed_2049_ = lean_unbox_usize(v_i_2046_);
lean_dec(v_i_2046_);
v_stop_boxed_2050_ = lean_unbox_usize(v_stop_2047_);
lean_dec(v_stop_2047_);
v_res_2051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(v_00_u03b1_2042_, v_00_u03b2_2043_, v_x_2044_, v_as_2045_, v_i_boxed_2049_, v_stop_boxed_2050_, v_b_2048_);
lean_dec_ref(v_as_2045_);
lean_dec(v_x_2044_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg(lean_object* v_m_2054_){
_start:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = ((lean_object*)(l_Lean_PersistentHashMap_stats___redArg___closed__0));
v___x_2056_ = lean_unsigned_to_nat(1u);
v___x_2057_ = l_Lean_PersistentHashMap_collectStats___redArg(v_m_2054_, v___x_2055_, v___x_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg___boxed(lean_object* v_m_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2058_);
lean_dec_ref(v_m_2058_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats(lean_object* v_00_u03b1_2060_, lean_object* v_00_u03b2_2061_, lean_object* v_x_2062_, lean_object* v_x_2063_, lean_object* v_m_2064_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___boxed(lean_object* v_00_u03b1_2066_, lean_object* v_00_u03b2_2067_, lean_object* v_x_2068_, lean_object* v_x_2069_, lean_object* v_m_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_PersistentHashMap_stats(v_00_u03b1_2066_, v_00_u03b2_2067_, v_x_2068_, v_x_2069_, v_m_2070_);
lean_dec_ref(v_m_2070_);
lean_dec_ref(v_x_2069_);
lean_dec_ref(v_x_2068_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Stats_toString(lean_object* v_s_2077_){
_start:
{
lean_object* v_numNodes_2078_; lean_object* v_numNull_2079_; lean_object* v_numCollisions_2080_; lean_object* v_maxDepth_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_numNodes_2078_ = lean_ctor_get(v_s_2077_, 0);
lean_inc(v_numNodes_2078_);
v_numNull_2079_ = lean_ctor_get(v_s_2077_, 1);
lean_inc(v_numNull_2079_);
v_numCollisions_2080_ = lean_ctor_get(v_s_2077_, 2);
lean_inc(v_numCollisions_2080_);
v_maxDepth_2081_ = lean_ctor_get(v_s_2077_, 3);
lean_inc(v_maxDepth_2081_);
lean_dec_ref(v_s_2077_);
v___x_2082_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__0));
v___x_2083_ = l_Nat_reprFast(v_numNodes_2078_);
v___x_2084_ = lean_string_append(v___x_2082_, v___x_2083_);
lean_dec_ref(v___x_2083_);
v___x_2085_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__1));
v___x_2086_ = lean_string_append(v___x_2084_, v___x_2085_);
v___x_2087_ = l_Nat_reprFast(v_numNull_2079_);
v___x_2088_ = lean_string_append(v___x_2086_, v___x_2087_);
lean_dec_ref(v___x_2087_);
v___x_2089_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__2));
v___x_2090_ = lean_string_append(v___x_2088_, v___x_2089_);
v___x_2091_ = l_Nat_reprFast(v_numCollisions_2080_);
v___x_2092_ = lean_string_append(v___x_2090_, v___x_2091_);
lean_dec_ref(v___x_2091_);
v___x_2093_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__3));
v___x_2094_ = lean_string_append(v___x_2092_, v___x_2093_);
v___x_2095_ = l_Nat_reprFast(v_maxDepth_2081_);
v___x_2096_ = lean_string_append(v___x_2094_, v___x_2095_);
lean_dec_ref(v___x_2095_);
v___x_2097_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__4));
v___x_2098_ = lean_string_append(v___x_2096_, v___x_2097_);
return v___x_2098_;
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
