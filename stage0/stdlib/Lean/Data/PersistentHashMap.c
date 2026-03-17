// Lean compiler output
// Module: Lean.Data.PersistentHashMap
// Imports: public import Init.Data.Array.BasicAux public import Init.Data.UInt.Basic public import Init.Control.Except public import Init.Data.Array.Basic import Init.Data.String.Defs import Init.Data.ToString.Macro
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_t_17_);
v___x_21_ = lean_apply_2(v_k_18_, v_key_19_, v_val_20_);
return v___x_21_;
}
case 1:
{
lean_object* v_node_22_; lean_object* v___x_23_; 
v_node_22_ = lean_ctor_get(v_t_17_, 0);
lean_inc(v_node_22_);
lean_dec_ref(v_t_17_);
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
lean_dec_ref(v_t_92_);
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
lean_dec_ref(v_t_92_);
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
lean_inc_ref(v_inst_453_);
lean_inc(v_k_461_);
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
lean_inc(v_k_461_);
lean_inc_ref(v_inst_453_);
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
lean_object* v_es_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_623_; 
v_es_601_ = lean_ctor_get(v_x_598_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_623_ == 0)
{
v___x_603_ = v_x_598_;
v_isShared_604_ = v_isSharedCheck_623_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_es_601_);
lean_dec(v_x_598_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_623_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; size_t v___x_606_; size_t v___x_607_; size_t v___x_608_; lean_object* v_j_609_; lean_object* v___x_610_; 
v___x_605_ = lean_box(2);
v___x_606_ = ((size_t)5ULL);
v___x_607_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_608_ = lean_usize_land(v_x_599_, v___x_607_);
v_j_609_ = lean_usize_to_nat(v___x_608_);
v___x_610_ = lean_array_get(v___x_605_, v_es_601_, v_j_609_);
lean_dec(v_j_609_);
lean_dec_ref(v_es_601_);
switch(lean_obj_tag(v___x_610_))
{
case 0:
{
lean_object* v_key_611_; lean_object* v_val_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_key_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_key_611_);
v_val_612_ = lean_ctor_get(v___x_610_, 1);
lean_inc(v_val_612_);
lean_dec_ref(v___x_610_);
v___x_613_ = lean_apply_2(v_inst_597_, v_x_600_, v_key_611_);
v___x_614_ = lean_unbox(v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
lean_dec(v_val_612_);
lean_del_object(v___x_603_);
v___x_615_ = lean_box(0);
return v___x_615_;
}
else
{
lean_object* v___x_617_; 
if (v_isShared_604_ == 0)
{
lean_ctor_set_tag(v___x_603_, 1);
lean_ctor_set(v___x_603_, 0, v_val_612_);
v___x_617_ = v___x_603_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_val_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
case 1:
{
lean_object* v_node_619_; size_t v___x_620_; 
lean_del_object(v___x_603_);
v_node_619_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_node_619_);
lean_dec_ref(v___x_610_);
v___x_620_ = lean_usize_shift_right(v_x_599_, v___x_606_);
v_x_598_ = v_node_619_;
v_x_599_ = v___x_620_;
goto _start;
}
default: 
{
lean_object* v___x_622_; 
lean_del_object(v___x_603_);
lean_dec(v_x_600_);
lean_dec_ref(v_inst_597_);
v___x_622_ = lean_box(0);
return v___x_622_;
}
}
}
}
else
{
lean_object* v_ks_624_; lean_object* v_vs_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_ks_624_ = lean_ctor_get(v_x_598_, 0);
lean_inc_ref(v_ks_624_);
v_vs_625_ = lean_ctor_get(v_x_598_, 1);
lean_inc_ref(v_vs_625_);
lean_dec_ref(v_x_598_);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_597_, v_ks_624_, v_vs_625_, v___x_626_, v_x_600_);
lean_dec_ref(v_vs_625_);
lean_dec_ref(v_ks_624_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg___boxed(lean_object* v_inst_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
size_t v_x_151__boxed_632_; lean_object* v_res_633_; 
v_x_151__boxed_632_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_res_633_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_628_, v_x_629_, v_x_151__boxed_632_, v_x_631_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux(lean_object* v_00_u03b1_634_, lean_object* v_00_u03b2_635_, lean_object* v_inst_636_, lean_object* v_x_637_, size_t v_x_638_, lean_object* v_x_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_636_, v_x_637_, v_x_638_, v_x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___boxed(lean_object* v_00_u03b1_641_, lean_object* v_00_u03b2_642_, lean_object* v_inst_643_, lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
size_t v_x_217__boxed_647_; lean_object* v_res_648_; 
v_x_217__boxed_647_ = lean_unbox_usize(v_x_645_);
lean_dec(v_x_645_);
v_res_648_ = l_Lean_PersistentHashMap_findAux(v_00_u03b1_641_, v_00_u03b2_642_, v_inst_643_, v_x_644_, v_x_217__boxed_647_, v_x_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object* v_x_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; uint64_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
lean_inc(v_x_652_);
v___x_653_ = lean_apply_1(v_x_650_, v_x_652_);
v___x_654_ = lean_unbox_uint64(v___x_653_);
lean_dec_ref(v___x_653_);
v___x_655_ = lean_uint64_to_usize(v___x_654_);
v___x_656_ = l_Lean_PersistentHashMap_findAux___redArg(v_x_649_, v_x_651_, v___x_655_, v_x_652_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f(lean_object* v_00_u03b1_657_, lean_object* v_00_u03b2_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_659_, v_x_660_, v_x_661_, v_x_662_);
return v___x_663_;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg(lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___f_672_; 
v___f_672_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0), 5, 2);
lean_closure_set(v___f_672_, 0, v_x_670_);
lean_closure_set(v___f_672_, 1, v_x_671_);
return v___f_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b2_674_, lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
lean_object* v___f_677_; 
v___f_677_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0), 5, 2);
lean_closure_set(v___f_677_, 0, v_x_675_);
lean_closure_set(v___f_677_, 1, v_x_676_);
return v___f_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg(lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_m_680_, lean_object* v_a_681_, lean_object* v_b_u2080_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_678_, v_x_679_, v_m_680_, v_a_681_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_inc(v_b_u2080_682_);
return v_b_u2080_682_;
}
else
{
lean_object* v_val_684_; 
v_val_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_val_684_);
lean_dec_ref(v___x_683_);
return v_val_684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg___boxed(lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_m_687_, lean_object* v_a_688_, lean_object* v_b_u2080_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_PersistentHashMap_findD___redArg(v_x_685_, v_x_686_, v_m_687_, v_a_688_, v_b_u2080_689_);
lean_dec(v_b_u2080_689_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_m_695_, lean_object* v_a_696_, lean_object* v_b_u2080_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_693_, v_x_694_, v_m_695_, v_a_696_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_inc(v_b_u2080_697_);
return v_b_u2080_697_;
}
else
{
lean_object* v_val_699_; 
v_val_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_val_699_);
lean_dec_ref(v___x_698_);
return v_val_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___boxed(lean_object* v_00_u03b1_700_, lean_object* v_00_u03b2_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_m_704_, lean_object* v_a_705_, lean_object* v_b_u2080_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_PersistentHashMap_findD(v_00_u03b1_700_, v_00_u03b2_701_, v_x_702_, v_x_703_, v_m_704_, v_a_705_, v_b_u2080_706_);
lean_dec(v_b_u2080_706_);
return v_res_707_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_711_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__2));
v___x_712_ = lean_unsigned_to_nat(14u);
v___x_713_ = lean_unsigned_to_nat(177u);
v___x_714_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__1));
v___x_715_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__0));
v___x_716_ = l_mkPanicMessageWithDecl(v___x_715_, v___x_714_, v___x_713_, v___x_712_, v___x_711_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg(lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_inst_719_, lean_object* v_m_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_717_, v_x_718_, v_m_720_, v_a_721_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_724_ = l_panic___redArg(v_inst_719_, v___x_723_);
return v___x_724_;
}
else
{
lean_object* v_val_725_; 
lean_dec(v_inst_719_);
v_val_725_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_val_725_);
lean_dec_ref(v___x_722_);
return v_val_725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21(lean_object* v_00_u03b1_726_, lean_object* v_00_u03b2_727_, lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_inst_730_, lean_object* v_m_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_728_, v_x_729_, v_m_731_, v_a_732_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_735_ = l_panic___redArg(v_inst_730_, v___x_734_);
return v___x_735_;
}
else
{
lean_object* v_val_736_; 
lean_dec(v_inst_730_);
v_val_736_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_val_736_);
lean_dec_ref(v___x_733_);
return v_val_736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg(lean_object* v_inst_737_, lean_object* v_keys_738_, lean_object* v_vals_739_, lean_object* v_i_740_, lean_object* v_k_741_){
_start:
{
lean_object* v___x_742_; uint8_t v___x_743_; 
v___x_742_ = lean_array_get_size(v_keys_738_);
v___x_743_ = lean_nat_dec_lt(v_i_740_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_dec(v_k_741_);
lean_dec(v_i_740_);
lean_dec_ref(v_inst_737_);
v___x_744_ = lean_box(0);
return v___x_744_;
}
else
{
lean_object* v_k_x27_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_k_x27_745_ = lean_array_fget_borrowed(v_keys_738_, v_i_740_);
lean_inc_ref(v_inst_737_);
lean_inc(v_k_x27_745_);
lean_inc(v_k_741_);
v___x_746_ = lean_apply_2(v_inst_737_, v_k_741_, v_k_x27_745_);
v___x_747_ = lean_unbox(v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = lean_nat_add(v_i_740_, v___x_748_);
lean_dec(v_i_740_);
v_i_740_ = v___x_749_;
goto _start;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec(v_k_741_);
lean_dec_ref(v_inst_737_);
v___x_751_ = lean_array_fget_borrowed(v_vals_739_, v_i_740_);
lean_dec(v_i_740_);
lean_inc(v___x_751_);
lean_inc(v_k_x27_745_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_k_x27_745_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg___boxed(lean_object* v_inst_754_, lean_object* v_keys_755_, lean_object* v_vals_756_, lean_object* v_i_757_, lean_object* v_k_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_754_, v_keys_755_, v_vals_756_, v_i_757_, v_k_758_);
lean_dec_ref(v_vals_756_);
lean_dec_ref(v_keys_755_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux(lean_object* v_00_u03b1_760_, lean_object* v_00_u03b2_761_, lean_object* v_inst_762_, lean_object* v_keys_763_, lean_object* v_vals_764_, lean_object* v_heq_765_, lean_object* v_i_766_, lean_object* v_k_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_762_, v_keys_763_, v_vals_764_, v_i_766_, v_k_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___boxed(lean_object* v_00_u03b1_769_, lean_object* v_00_u03b2_770_, lean_object* v_inst_771_, lean_object* v_keys_772_, lean_object* v_vals_773_, lean_object* v_heq_774_, lean_object* v_i_775_, lean_object* v_k_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_PersistentHashMap_findEntryAtAux(v_00_u03b1_769_, v_00_u03b2_770_, v_inst_771_, v_keys_772_, v_vals_773_, v_heq_774_, v_i_775_, v_k_776_);
lean_dec_ref(v_vals_773_);
lean_dec_ref(v_keys_772_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg(lean_object* v_inst_778_, lean_object* v_x_779_, size_t v_x_780_, lean_object* v_x_781_){
_start:
{
if (lean_obj_tag(v_x_779_) == 0)
{
lean_object* v_es_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_811_; 
v_es_782_ = lean_ctor_get(v_x_779_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_x_779_);
if (v_isSharedCheck_811_ == 0)
{
v___x_784_ = v_x_779_;
v_isShared_785_ = v_isSharedCheck_811_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_es_782_);
lean_dec(v_x_779_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_811_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; size_t v___x_787_; size_t v___x_788_; size_t v___x_789_; lean_object* v_j_790_; lean_object* v___x_791_; 
v___x_786_ = lean_box(2);
v___x_787_ = ((size_t)5ULL);
v___x_788_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_789_ = lean_usize_land(v_x_780_, v___x_788_);
v_j_790_ = lean_usize_to_nat(v___x_789_);
v___x_791_ = lean_array_get(v___x_786_, v_es_782_, v_j_790_);
lean_dec(v_j_790_);
lean_dec_ref(v_es_782_);
switch(lean_obj_tag(v___x_791_))
{
case 0:
{
lean_object* v_key_792_; lean_object* v_val_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_806_; 
v_key_792_ = lean_ctor_get(v___x_791_, 0);
v_val_793_ = lean_ctor_get(v___x_791_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_806_ == 0)
{
v___x_795_ = v___x_791_;
v_isShared_796_ = v_isSharedCheck_806_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_val_793_);
lean_inc(v_key_792_);
lean_dec(v___x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_806_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; uint8_t v___x_798_; 
lean_inc(v_key_792_);
v___x_797_ = lean_apply_2(v_inst_778_, v_x_781_, v_key_792_);
v___x_798_ = lean_unbox(v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; 
lean_del_object(v___x_795_);
lean_dec(v_val_793_);
lean_dec(v_key_792_);
lean_del_object(v___x_784_);
v___x_799_ = lean_box(0);
return v___x_799_;
}
else
{
lean_object* v___x_801_; 
if (v_isShared_796_ == 0)
{
v___x_801_ = v___x_795_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_key_792_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_val_793_);
v___x_801_ = v_reuseFailAlloc_805_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set_tag(v___x_784_, 1);
lean_ctor_set(v___x_784_, 0, v___x_801_);
v___x_803_ = v___x_784_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
case 1:
{
lean_object* v_node_807_; size_t v___x_808_; 
lean_del_object(v___x_784_);
v_node_807_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_node_807_);
lean_dec_ref(v___x_791_);
v___x_808_ = lean_usize_shift_right(v_x_780_, v___x_787_);
v_x_779_ = v_node_807_;
v_x_780_ = v___x_808_;
goto _start;
}
default: 
{
lean_object* v___x_810_; 
lean_del_object(v___x_784_);
lean_dec(v_x_781_);
lean_dec_ref(v_inst_778_);
v___x_810_ = lean_box(0);
return v___x_810_;
}
}
}
}
else
{
lean_object* v_ks_812_; lean_object* v_vs_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v_ks_812_ = lean_ctor_get(v_x_779_, 0);
lean_inc_ref(v_ks_812_);
v_vs_813_ = lean_ctor_get(v_x_779_, 1);
lean_inc_ref(v_vs_813_);
lean_dec_ref(v_x_779_);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_778_, v_ks_812_, v_vs_813_, v___x_814_, v_x_781_);
lean_dec_ref(v_vs_813_);
lean_dec_ref(v_ks_812_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg___boxed(lean_object* v_inst_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
size_t v_x_155__boxed_820_; lean_object* v_res_821_; 
v_x_155__boxed_820_ = lean_unbox_usize(v_x_818_);
lean_dec(v_x_818_);
v_res_821_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_816_, v_x_817_, v_x_155__boxed_820_, v_x_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux(lean_object* v_00_u03b1_822_, lean_object* v_00_u03b2_823_, lean_object* v_inst_824_, lean_object* v_x_825_, size_t v_x_826_, lean_object* v_x_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_824_, v_x_825_, v_x_826_, v_x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___boxed(lean_object* v_00_u03b1_829_, lean_object* v_00_u03b2_830_, lean_object* v_inst_831_, lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_x_834_){
_start:
{
size_t v_x_235__boxed_835_; lean_object* v_res_836_; 
v_x_235__boxed_835_ = lean_unbox_usize(v_x_833_);
lean_dec(v_x_833_);
v_res_836_ = l_Lean_PersistentHashMap_findEntryAux(v_00_u03b1_829_, v_00_u03b2_830_, v_inst_831_, v_x_832_, v_x_235__boxed_835_, v_x_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
lean_object* v___x_841_; uint64_t v___x_842_; size_t v___x_843_; lean_object* v___x_844_; 
lean_inc(v_x_840_);
v___x_841_ = lean_apply_1(v_x_838_, v_x_840_);
v___x_842_ = lean_unbox_uint64(v___x_841_);
lean_dec_ref(v___x_841_);
v___x_843_ = lean_uint64_to_usize(v___x_842_);
v___x_844_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_x_837_, v_x_839_, v___x_843_, v_x_840_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f(lean_object* v_00_u03b1_845_, lean_object* v_00_u03b2_846_, lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_x_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_847_, v_x_848_, v_x_849_, v_x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg(lean_object* v_inst_852_, lean_object* v_keys_853_, lean_object* v_i_854_, lean_object* v_k_855_, lean_object* v_k_u2080_856_){
_start:
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = lean_array_get_size(v_keys_853_);
v___x_858_ = lean_nat_dec_lt(v_i_854_, v___x_857_);
if (v___x_858_ == 0)
{
lean_dec(v_k_855_);
lean_dec(v_i_854_);
lean_dec_ref(v_inst_852_);
lean_inc(v_k_u2080_856_);
return v_k_u2080_856_;
}
else
{
lean_object* v_k_x27_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_k_x27_859_ = lean_array_fget_borrowed(v_keys_853_, v_i_854_);
lean_inc_ref(v_inst_852_);
lean_inc(v_k_x27_859_);
lean_inc(v_k_855_);
v___x_860_ = lean_apply_2(v_inst_852_, v_k_855_, v_k_x27_859_);
v___x_861_ = lean_unbox(v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(1u);
v___x_863_ = lean_nat_add(v_i_854_, v___x_862_);
lean_dec(v_i_854_);
v_i_854_ = v___x_863_;
goto _start;
}
else
{
lean_dec(v_k_855_);
lean_dec(v_i_854_);
lean_dec_ref(v_inst_852_);
lean_inc(v_k_x27_859_);
return v_k_x27_859_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg___boxed(lean_object* v_inst_865_, lean_object* v_keys_866_, lean_object* v_i_867_, lean_object* v_k_868_, lean_object* v_k_u2080_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_865_, v_keys_866_, v_i_867_, v_k_868_, v_k_u2080_869_);
lean_dec(v_k_u2080_869_);
lean_dec_ref(v_keys_866_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux(lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_inst_873_, lean_object* v_keys_874_, lean_object* v_vals_875_, lean_object* v_heq_876_, lean_object* v_i_877_, lean_object* v_k_878_, lean_object* v_k_u2080_879_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_873_, v_keys_874_, v_i_877_, v_k_878_, v_k_u2080_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___boxed(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_inst_883_, lean_object* v_keys_884_, lean_object* v_vals_885_, lean_object* v_heq_886_, lean_object* v_i_887_, lean_object* v_k_888_, lean_object* v_k_u2080_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_PersistentHashMap_findKeyDAtAux(v_00_u03b1_881_, v_00_u03b2_882_, v_inst_883_, v_keys_884_, v_vals_885_, v_heq_886_, v_i_887_, v_k_888_, v_k_u2080_889_);
lean_dec(v_k_u2080_889_);
lean_dec_ref(v_vals_885_);
lean_dec_ref(v_keys_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object* v_inst_891_, lean_object* v_x_892_, size_t v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
if (lean_obj_tag(v_x_892_) == 0)
{
lean_object* v_es_896_; lean_object* v___x_897_; size_t v___x_898_; size_t v___x_899_; size_t v___x_900_; lean_object* v_j_901_; lean_object* v___x_902_; 
v_es_896_ = lean_ctor_get(v_x_892_, 0);
lean_inc_ref(v_es_896_);
lean_dec_ref(v_x_892_);
v___x_897_ = lean_box(2);
v___x_898_ = ((size_t)5ULL);
v___x_899_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_900_ = lean_usize_land(v_x_893_, v___x_899_);
v_j_901_ = lean_usize_to_nat(v___x_900_);
v___x_902_ = lean_array_get(v___x_897_, v_es_896_, v_j_901_);
lean_dec(v_j_901_);
lean_dec_ref(v_es_896_);
switch(lean_obj_tag(v___x_902_))
{
case 0:
{
lean_object* v_key_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_key_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_key_903_);
lean_dec_ref(v___x_902_);
lean_inc(v_key_903_);
v___x_904_ = lean_apply_2(v_inst_891_, v_x_894_, v_key_903_);
v___x_905_ = lean_unbox(v___x_904_);
if (v___x_905_ == 0)
{
lean_dec(v_key_903_);
lean_inc(v_x_895_);
return v_x_895_;
}
else
{
return v_key_903_;
}
}
case 1:
{
lean_object* v_node_906_; size_t v___x_907_; 
v_node_906_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_node_906_);
lean_dec_ref(v___x_902_);
v___x_907_ = lean_usize_shift_right(v_x_893_, v___x_898_);
v_x_892_ = v_node_906_;
v_x_893_ = v___x_907_;
goto _start;
}
default: 
{
lean_dec(v_x_894_);
lean_dec_ref(v_inst_891_);
lean_inc(v_x_895_);
return v_x_895_;
}
}
}
else
{
lean_object* v_ks_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_ks_909_ = lean_ctor_get(v_x_892_, 0);
lean_inc_ref(v_ks_909_);
lean_dec_ref(v_x_892_);
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_891_, v_ks_909_, v___x_910_, v_x_894_, v_x_895_);
lean_dec_ref(v_ks_909_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg___boxed(lean_object* v_inst_912_, lean_object* v_x_913_, lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
size_t v_x_140__boxed_917_; lean_object* v_res_918_; 
v_x_140__boxed_917_ = lean_unbox_usize(v_x_914_);
lean_dec(v_x_914_);
v_res_918_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_912_, v_x_913_, v_x_140__boxed_917_, v_x_915_, v_x_916_);
lean_dec(v_x_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux(lean_object* v_00_u03b1_919_, lean_object* v_00_u03b2_920_, lean_object* v_inst_921_, lean_object* v_x_922_, size_t v_x_923_, lean_object* v_x_924_, lean_object* v_x_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_921_, v_x_922_, v_x_923_, v_x_924_, v_x_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___boxed(lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v_inst_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_x_933_){
_start:
{
size_t v_x_189__boxed_934_; lean_object* v_res_935_; 
v_x_189__boxed_934_ = lean_unbox_usize(v_x_931_);
lean_dec(v_x_931_);
v_res_935_ = l_Lean_PersistentHashMap_findKeyDAux(v_00_u03b1_927_, v_00_u03b2_928_, v_inst_929_, v_x_930_, v_x_189__boxed_934_, v_x_932_, v_x_933_);
lean_dec(v_x_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg(lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_m_938_, lean_object* v_a_939_, lean_object* v_a_u2080_940_){
_start:
{
lean_object* v___x_941_; uint64_t v___x_942_; size_t v___x_943_; lean_object* v___x_944_; 
lean_inc(v_a_939_);
v___x_941_ = lean_apply_1(v_x_937_, v_a_939_);
v___x_942_ = lean_unbox_uint64(v___x_941_);
lean_dec_ref(v___x_941_);
v___x_943_ = lean_uint64_to_usize(v___x_942_);
v___x_944_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_936_, v_m_938_, v___x_943_, v_a_939_, v_a_u2080_940_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg___boxed(lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_m_947_, lean_object* v_a_948_, lean_object* v_a_u2080_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_PersistentHashMap_findKeyD___redArg(v_x_945_, v_x_946_, v_m_947_, v_a_948_, v_a_u2080_949_);
lean_dec(v_a_u2080_949_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD(lean_object* v_00_u03b1_951_, lean_object* v_00_u03b2_952_, lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_m_955_, lean_object* v_a_956_, lean_object* v_a_u2080_957_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___boxed(lean_object* v_00_u03b1_962_, lean_object* v_00_u03b2_963_, lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_m_966_, lean_object* v_a_967_, lean_object* v_a_u2080_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_PersistentHashMap_findKeyD(v_00_u03b1_962_, v_00_u03b2_963_, v_x_964_, v_x_965_, v_m_966_, v_a_967_, v_a_u2080_968_);
lean_dec(v_a_u2080_968_);
return v_res_969_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___redArg(lean_object* v_inst_970_, lean_object* v_keys_971_, lean_object* v_i_972_, lean_object* v_k_973_){
_start:
{
lean_object* v___x_974_; uint8_t v___x_975_; 
v___x_974_ = lean_array_get_size(v_keys_971_);
v___x_975_ = lean_nat_dec_lt(v_i_972_, v___x_974_);
if (v___x_975_ == 0)
{
lean_dec(v_k_973_);
lean_dec(v_i_972_);
lean_dec_ref(v_inst_970_);
return v___x_975_;
}
else
{
lean_object* v_k_x27_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_k_x27_976_ = lean_array_fget_borrowed(v_keys_971_, v_i_972_);
lean_inc_ref(v_inst_970_);
lean_inc(v_k_x27_976_);
lean_inc(v_k_973_);
v___x_977_ = lean_apply_2(v_inst_970_, v_k_973_, v_k_x27_976_);
v___x_978_ = lean_unbox(v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_unsigned_to_nat(1u);
v___x_980_ = lean_nat_add(v_i_972_, v___x_979_);
lean_dec(v_i_972_);
v_i_972_ = v___x_980_;
goto _start;
}
else
{
uint8_t v___x_982_; 
lean_dec(v_k_973_);
lean_dec(v_i_972_);
lean_dec_ref(v_inst_970_);
v___x_982_ = lean_unbox(v___x_977_);
return v___x_982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___redArg___boxed(lean_object* v_inst_983_, lean_object* v_keys_984_, lean_object* v_i_985_, lean_object* v_k_986_){
_start:
{
uint8_t v_res_987_; lean_object* v_r_988_; 
v_res_987_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_983_, v_keys_984_, v_i_985_, v_k_986_);
lean_dec_ref(v_keys_984_);
v_r_988_ = lean_box(v_res_987_);
return v_r_988_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux(lean_object* v_00_u03b1_989_, lean_object* v_00_u03b2_990_, lean_object* v_inst_991_, lean_object* v_keys_992_, lean_object* v_vals_993_, lean_object* v_heq_994_, lean_object* v_i_995_, lean_object* v_k_996_){
_start:
{
uint8_t v___x_997_; 
v___x_997_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_991_, v_keys_992_, v_i_995_, v_k_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___boxed(lean_object* v_00_u03b1_998_, lean_object* v_00_u03b2_999_, lean_object* v_inst_1000_, lean_object* v_keys_1001_, lean_object* v_vals_1002_, lean_object* v_heq_1003_, lean_object* v_i_1004_, lean_object* v_k_1005_){
_start:
{
uint8_t v_res_1006_; lean_object* v_r_1007_; 
v_res_1006_ = l_Lean_PersistentHashMap_containsAtAux(v_00_u03b1_998_, v_00_u03b2_999_, v_inst_1000_, v_keys_1001_, v_vals_1002_, v_heq_1003_, v_i_1004_, v_k_1005_);
lean_dec_ref(v_vals_1002_);
lean_dec_ref(v_keys_1001_);
v_r_1007_ = lean_box(v_res_1006_);
return v_r_1007_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___redArg(lean_object* v_inst_1008_, lean_object* v_x_1009_, size_t v_x_1010_, lean_object* v_x_1011_){
_start:
{
if (lean_obj_tag(v_x_1009_) == 0)
{
lean_object* v_es_1012_; lean_object* v___x_1013_; size_t v___x_1014_; size_t v___x_1015_; size_t v___x_1016_; lean_object* v_j_1017_; lean_object* v___x_1018_; 
v_es_1012_ = lean_ctor_get(v_x_1009_, 0);
lean_inc_ref(v_es_1012_);
lean_dec_ref(v_x_1009_);
v___x_1013_ = lean_box(2);
v___x_1014_ = ((size_t)5ULL);
v___x_1015_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_1016_ = lean_usize_land(v_x_1010_, v___x_1015_);
v_j_1017_ = lean_usize_to_nat(v___x_1016_);
v___x_1018_ = lean_array_get(v___x_1013_, v_es_1012_, v_j_1017_);
lean_dec(v_j_1017_);
lean_dec_ref(v_es_1012_);
switch(lean_obj_tag(v___x_1018_))
{
case 0:
{
lean_object* v_key_1019_; lean_object* v___x_1020_; uint8_t v___x_1021_; 
v_key_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_key_1019_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = lean_apply_2(v_inst_1008_, v_x_1011_, v_key_1019_);
v___x_1021_ = lean_unbox(v___x_1020_);
return v___x_1021_;
}
case 1:
{
lean_object* v_node_1022_; size_t v___x_1023_; 
v_node_1022_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_node_1022_);
lean_dec_ref(v___x_1018_);
v___x_1023_ = lean_usize_shift_right(v_x_1010_, v___x_1014_);
v_x_1009_ = v_node_1022_;
v_x_1010_ = v___x_1023_;
goto _start;
}
default: 
{
uint8_t v___x_1025_; 
lean_dec(v_x_1011_);
lean_dec_ref(v_inst_1008_);
v___x_1025_ = 0;
return v___x_1025_;
}
}
}
else
{
lean_object* v_ks_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v_ks_1026_ = lean_ctor_get(v_x_1009_, 0);
lean_inc_ref(v_ks_1026_);
lean_dec_ref(v_x_1009_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1008_, v_ks_1026_, v___x_1027_, v_x_1011_);
lean_dec_ref(v_ks_1026_);
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___redArg___boxed(lean_object* v_inst_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_x_1032_){
_start:
{
size_t v_x_110__boxed_1033_; uint8_t v_res_1034_; lean_object* v_r_1035_; 
v_x_110__boxed_1033_ = lean_unbox_usize(v_x_1031_);
lean_dec(v_x_1031_);
v_res_1034_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1029_, v_x_1030_, v_x_110__boxed_1033_, v_x_1032_);
v_r_1035_ = lean_box(v_res_1034_);
return v_r_1035_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux(lean_object* v_00_u03b1_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_inst_1038_, lean_object* v_x_1039_, size_t v_x_1040_, lean_object* v_x_1041_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1038_, v_x_1039_, v_x_1040_, v_x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_00_u03b2_1044_, lean_object* v_inst_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
size_t v_x_158__boxed_1049_; uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_x_158__boxed_1049_ = lean_unbox_usize(v_x_1047_);
lean_dec(v_x_1047_);
v_res_1050_ = l_Lean_PersistentHashMap_containsAux(v_00_u03b1_1043_, v_00_u03b2_1044_, v_inst_1045_, v_x_1046_, v_x_158__boxed_1049_, v_x_1048_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
lean_object* v___x_1056_; uint64_t v___x_1057_; size_t v___x_1058_; uint8_t v___x_1059_; 
lean_inc(v_x_1055_);
v___x_1056_ = lean_apply_1(v_inst_1053_, v_x_1055_);
v___x_1057_ = lean_unbox_uint64(v___x_1056_);
lean_dec_ref(v___x_1056_);
v___x_1058_ = lean_uint64_to_usize(v___x_1057_);
v___x_1059_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1052_, v_x_1054_, v___x_1058_, v_x_1055_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___redArg___boxed(lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_){
_start:
{
uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_res_1064_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1060_, v_inst_1061_, v_x_1062_, v_x_1063_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains(lean_object* v_00_u03b1_1066_, lean_object* v_00_u03b2_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
uint8_t v___x_1072_; 
v___x_1072_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1068_, v_inst_1069_, v_x_1070_, v_x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___boxed(lean_object* v_00_u03b1_1073_, lean_object* v_00_u03b2_1074_, lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l_Lean_PersistentHashMap_contains(v_00_u03b1_1073_, v_00_u03b2_1074_, v_inst_1075_, v_inst_1076_, v_x_1077_, v_x_1078_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg(lean_object* v_a_1081_, lean_object* v_i_1082_, lean_object* v_acc_1083_){
_start:
{
lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1084_ = lean_array_get_size(v_a_1081_);
v___x_1085_ = lean_nat_dec_lt(v_i_1082_, v___x_1084_);
if (v___x_1085_ == 0)
{
lean_dec(v_i_1082_);
return v_acc_1083_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_array_fget(v_a_1081_, v_i_1082_);
switch(lean_obj_tag(v___x_1086_))
{
case 0:
{
if (lean_obj_tag(v_acc_1083_) == 0)
{
lean_object* v_key_1087_; lean_object* v_val_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1099_; 
v_key_1087_ = lean_ctor_get(v___x_1086_, 0);
v_val_1088_ = lean_ctor_get(v___x_1086_, 1);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1090_ = v___x_1086_;
v_isShared_1091_ = v_isSharedCheck_1099_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_val_1088_);
lean_inc(v_key_1087_);
lean_dec(v___x_1086_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1099_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_nat_add(v_i_1082_, v___x_1092_);
lean_dec(v_i_1082_);
if (v_isShared_1091_ == 0)
{
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_key_1087_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v_val_1088_);
v___x_1095_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
v_i_1082_ = v___x_1093_;
v_acc_1083_ = v___x_1096_;
goto _start;
}
}
}
else
{
lean_object* v___x_1100_; 
lean_dec_ref(v_acc_1083_);
lean_dec_ref(v___x_1086_);
lean_dec(v_i_1082_);
v___x_1100_ = lean_box(0);
return v___x_1100_;
}
}
case 1:
{
lean_object* v___x_1101_; 
lean_dec_ref(v___x_1086_);
lean_dec(v_acc_1083_);
lean_dec(v_i_1082_);
v___x_1101_ = lean_box(0);
return v___x_1101_;
}
default: 
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_unsigned_to_nat(1u);
v___x_1103_ = lean_nat_add(v_i_1082_, v___x_1102_);
lean_dec(v_i_1082_);
v_i_1082_ = v___x_1103_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg___boxed(lean_object* v_a_1105_, lean_object* v_i_1106_, lean_object* v_acc_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1105_, v_i_1106_, v_acc_1107_);
lean_dec_ref(v_a_1105_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries(lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_a_1111_, lean_object* v_i_1112_, lean_object* v_acc_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1111_, v_i_1112_, v_acc_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___boxed(lean_object* v_00_u03b1_1115_, lean_object* v_00_u03b2_1116_, lean_object* v_a_1117_, lean_object* v_i_1118_, lean_object* v_acc_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_PersistentHashMap_isUnaryEntries(v_00_u03b1_1115_, v_00_u03b2_1116_, v_a_1117_, v_i_1118_, v_acc_1119_);
lean_dec_ref(v_a_1117_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object* v_x_1121_){
_start:
{
if (lean_obj_tag(v_x_1121_) == 0)
{
lean_object* v_es_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_es_1122_ = lean_ctor_get(v_x_1121_, 0);
lean_inc_ref(v_es_1122_);
lean_dec_ref(v_x_1121_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_box(0);
v___x_1125_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_es_1122_, v___x_1123_, v___x_1124_);
lean_dec_ref(v_es_1122_);
return v___x_1125_;
}
else
{
lean_object* v_ks_1126_; lean_object* v_vs_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1142_; 
v_ks_1126_ = lean_ctor_get(v_x_1121_, 0);
v_vs_1127_ = lean_ctor_get(v_x_1121_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_x_1121_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1129_ = v_x_1121_;
v_isShared_1130_ = v_isSharedCheck_1142_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_vs_1127_);
lean_inc(v_ks_1126_);
lean_dec(v_x_1121_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1142_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_array_get_size(v_ks_1126_);
v___x_1133_ = lean_nat_dec_eq(v___x_1131_, v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; 
lean_del_object(v___x_1129_);
lean_dec_ref(v_vs_1127_);
lean_dec_ref(v_ks_1126_);
v___x_1134_ = lean_box(0);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1136_ = lean_array_fget(v_ks_1126_, v___x_1135_);
lean_dec_ref(v_ks_1126_);
v___x_1137_ = lean_array_fget(v_vs_1127_, v___x_1135_);
lean_dec_ref(v_vs_1127_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 0);
lean_ctor_set(v___x_1129_, 1, v___x_1137_);
lean_ctor_set(v___x_1129_, 0, v___x_1136_);
v___x_1139_ = v___x_1129_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1137_);
v___x_1139_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; 
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
return v___x_1140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode(lean_object* v_00_u03b1_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_x_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_x_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg(lean_object* v_inst_1147_, lean_object* v_x_1148_, size_t v_x_1149_, lean_object* v_x_1150_){
_start:
{
if (lean_obj_tag(v_x_1148_) == 0)
{
lean_object* v_es_1151_; lean_object* v___x_1152_; size_t v___x_1153_; size_t v___x_1154_; size_t v___x_1155_; lean_object* v_j_1156_; lean_object* v_entry_1157_; 
v_es_1151_ = lean_ctor_get(v_x_1148_, 0);
v___x_1152_ = lean_box(2);
v___x_1153_ = ((size_t)5ULL);
v___x_1154_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_1155_ = lean_usize_land(v_x_1149_, v___x_1154_);
v_j_1156_ = lean_usize_to_nat(v___x_1155_);
v_entry_1157_ = lean_array_get(v___x_1152_, v_es_1151_, v_j_1156_);
switch(lean_obj_tag(v_entry_1157_))
{
case 0:
{
lean_object* v_key_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v_key_1158_ = lean_ctor_get(v_entry_1157_, 0);
lean_inc(v_key_1158_);
lean_dec_ref(v_entry_1157_);
v___x_1159_ = lean_apply_2(v_inst_1147_, v_x_1150_, v_key_1158_);
v___x_1160_ = lean_unbox(v___x_1159_);
if (v___x_1160_ == 0)
{
lean_dec(v_j_1156_);
return v_x_1148_;
}
else
{
lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1168_; 
lean_inc_ref(v_es_1151_);
v_isSharedCheck_1168_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; 
v_unused_1169_ = lean_ctor_get(v_x_1148_, 0);
lean_dec(v_unused_1169_);
v___x_1162_ = v_x_1148_;
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
else
{
lean_dec(v_x_1148_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = lean_array_set(v_es_1151_, v_j_1156_, v___x_1152_);
lean_dec(v_j_1156_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
case 1:
{
lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1203_; 
lean_inc_ref(v_es_1151_);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1203_ == 0)
{
lean_object* v_unused_1204_; 
v_unused_1204_ = lean_ctor_get(v_x_1148_, 0);
lean_dec(v_unused_1204_);
v___x_1171_ = v_x_1148_;
v_isShared_1172_ = v_isSharedCheck_1203_;
goto v_resetjp_1170_;
}
else
{
lean_dec(v_x_1148_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1203_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_node_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1202_; 
v_node_1173_ = lean_ctor_get(v_entry_1157_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_entry_1157_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1175_ = v_entry_1157_;
v_isShared_1176_ = v_isSharedCheck_1202_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_node_1173_);
lean_dec(v_entry_1157_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1202_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_entries_1177_; size_t v___x_1178_; lean_object* v_newNode_1179_; lean_object* v___x_1180_; 
v_entries_1177_ = lean_array_set(v_es_1151_, v_j_1156_, v___x_1152_);
v___x_1178_ = lean_usize_shift_right(v_x_1149_, v___x_1153_);
v_newNode_1179_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1147_, v_node_1173_, v___x_1178_, v_x_1150_);
lean_inc_ref(v_newNode_1179_);
v___x_1180_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1179_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v___x_1182_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v_newNode_1179_);
v___x_1182_ = v___x_1175_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_newNode_1179_);
v___x_1182_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_array_set(v_entries_1177_, v_j_1156_, v___x_1182_);
lean_dec(v_j_1156_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1183_);
v___x_1185_ = v___x_1171_;
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
else
{
lean_object* v_val_1188_; lean_object* v_fst_1189_; lean_object* v_snd_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1201_; 
lean_dec_ref(v_newNode_1179_);
lean_del_object(v___x_1175_);
v_val_1188_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_val_1188_);
lean_dec_ref(v___x_1180_);
v_fst_1189_ = lean_ctor_get(v_val_1188_, 0);
v_snd_1190_ = lean_ctor_get(v_val_1188_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_val_1188_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1192_ = v_val_1188_;
v_isShared_1193_ = v_isSharedCheck_1201_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_snd_1190_);
lean_inc(v_fst_1189_);
lean_dec(v_val_1188_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1201_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_fst_1189_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_snd_1190_);
v___x_1195_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
v___x_1196_ = lean_array_set(v_entries_1177_, v_j_1156_, v___x_1195_);
lean_dec(v_j_1156_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1196_);
v___x_1198_ = v___x_1171_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1156_);
lean_dec(v_x_1150_);
lean_dec_ref(v_inst_1147_);
return v_x_1148_;
}
}
}
else
{
lean_object* v_ks_1205_; lean_object* v_vs_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1220_; 
v_ks_1205_ = lean_ctor_get(v_x_1148_, 0);
v_vs_1206_ = lean_ctor_get(v_x_1148_, 1);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1208_ = v_x_1148_;
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_vs_1206_);
lean_inc(v_ks_1205_);
lean_dec(v_x_1148_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1220_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Array_finIdxOf_x3f___redArg(v_inst_1147_, v_ks_1205_, v_x_1150_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v___x_1212_; 
if (v_isShared_1209_ == 0)
{
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_ks_1205_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_vs_1206_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
else
{
lean_object* v_val_1214_; lean_object* v_keys_x27_1215_; lean_object* v_vals_x27_1216_; lean_object* v___x_1218_; 
v_val_1214_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_val_1214_);
lean_dec_ref(v___x_1210_);
lean_inc(v_val_1214_);
v_keys_x27_1215_ = l_Array_eraseIdx___redArg(v_ks_1205_, v_val_1214_);
v_vals_x27_1216_ = l_Array_eraseIdx___redArg(v_vs_1206_, v_val_1214_);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 1, v_vals_x27_1216_);
lean_ctor_set(v___x_1208_, 0, v_keys_x27_1215_);
v___x_1218_ = v___x_1208_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_keys_x27_1215_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_vals_x27_1216_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg___boxed(lean_object* v_inst_1221_, lean_object* v_x_1222_, lean_object* v_x_1223_, lean_object* v_x_1224_){
_start:
{
size_t v_x_232__boxed_1225_; lean_object* v_res_1226_; 
v_x_232__boxed_1225_ = lean_unbox_usize(v_x_1223_);
lean_dec(v_x_1223_);
v_res_1226_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1221_, v_x_1222_, v_x_232__boxed_1225_, v_x_1224_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux(lean_object* v_00_u03b1_1227_, lean_object* v_00_u03b2_1228_, lean_object* v_inst_1229_, lean_object* v_x_1230_, size_t v_x_1231_, lean_object* v_x_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1229_, v_x_1230_, v_x_1231_, v_x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___boxed(lean_object* v_00_u03b1_1234_, lean_object* v_00_u03b2_1235_, lean_object* v_inst_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_, lean_object* v_x_1239_){
_start:
{
size_t v_x_375__boxed_1240_; lean_object* v_res_1241_; 
v_x_375__boxed_1240_ = lean_unbox_usize(v_x_1238_);
lean_dec(v_x_1238_);
v_res_1241_ = l_Lean_PersistentHashMap_eraseAux(v_00_u03b1_1234_, v_00_u03b2_1235_, v_inst_1236_, v_x_1237_, v_x_375__boxed_1240_, v_x_1239_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object* v_x_1242_, lean_object* v_x_1243_, lean_object* v_x_1244_, lean_object* v_x_1245_){
_start:
{
lean_object* v___x_1246_; uint64_t v___x_1247_; size_t v_h_1248_; lean_object* v___x_1249_; 
lean_inc(v_x_1245_);
v___x_1246_ = lean_apply_1(v_x_1243_, v_x_1245_);
v___x_1247_ = lean_unbox_uint64(v___x_1246_);
lean_dec_ref(v___x_1246_);
v_h_1248_ = lean_uint64_to_usize(v___x_1247_);
v___x_1249_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_x_1242_, v_x_1244_, v_h_1248_, v_x_1245_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase(lean_object* v_00_u03b1_1250_, lean_object* v_00_u03b2_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_, lean_object* v_x_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_PersistentHashMap_erase___redArg(v_x_1252_, v_x_1253_, v_x_1254_, v_x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed(lean_object* v_i_1257_, lean_object* v_inst_1258_, lean_object* v_f_1259_, lean_object* v_keys_1260_, lean_object* v_vals_1261_, lean_object* v_____do__lift_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(v_i_1257_, v_inst_1258_, v_f_1259_, v_keys_1260_, v_vals_1261_, v_____do__lift_1262_);
lean_dec(v_i_1257_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(lean_object* v_inst_1264_, lean_object* v_f_1265_, lean_object* v_keys_1266_, lean_object* v_vals_1267_, lean_object* v_i_1268_, lean_object* v_acc_1269_){
_start:
{
lean_object* v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = lean_array_get_size(v_keys_1266_);
v___x_1271_ = lean_nat_dec_lt(v_i_1268_, v___x_1270_);
if (v___x_1271_ == 0)
{
lean_object* v_toApplicative_1272_; lean_object* v_toPure_1273_; lean_object* v___x_1274_; 
lean_dec(v_i_1268_);
lean_dec_ref(v_vals_1267_);
lean_dec_ref(v_keys_1266_);
lean_dec(v_f_1265_);
v_toApplicative_1272_ = lean_ctor_get(v_inst_1264_, 0);
lean_inc_ref(v_toApplicative_1272_);
lean_dec_ref(v_inst_1264_);
v_toPure_1273_ = lean_ctor_get(v_toApplicative_1272_, 1);
lean_inc(v_toPure_1273_);
lean_dec_ref(v_toApplicative_1272_);
v___x_1274_ = lean_apply_2(v_toPure_1273_, lean_box(0), v_acc_1269_);
return v___x_1274_;
}
else
{
lean_object* v_toBind_1275_; lean_object* v___f_1276_; lean_object* v_k_1277_; lean_object* v_v_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v_toBind_1275_ = lean_ctor_get(v_inst_1264_, 1);
lean_inc(v_toBind_1275_);
lean_inc_ref(v_vals_1267_);
lean_inc_ref(v_keys_1266_);
lean_inc(v_f_1265_);
lean_inc(v_i_1268_);
v___f_1276_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1276_, 0, v_i_1268_);
lean_closure_set(v___f_1276_, 1, v_inst_1264_);
lean_closure_set(v___f_1276_, 2, v_f_1265_);
lean_closure_set(v___f_1276_, 3, v_keys_1266_);
lean_closure_set(v___f_1276_, 4, v_vals_1267_);
v_k_1277_ = lean_array_fget(v_keys_1266_, v_i_1268_);
lean_dec_ref(v_keys_1266_);
v_v_1278_ = lean_array_fget(v_vals_1267_, v_i_1268_);
lean_dec(v_i_1268_);
lean_dec_ref(v_vals_1267_);
v___x_1279_ = lean_apply_3(v_f_1265_, v_acc_1269_, v_k_1277_, v_v_1278_);
v___x_1280_ = lean_apply_4(v_toBind_1275_, lean_box(0), lean_box(0), v___x_1279_, v___f_1276_);
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(lean_object* v_i_1281_, lean_object* v_inst_1282_, lean_object* v_f_1283_, lean_object* v_keys_1284_, lean_object* v_vals_1285_, lean_object* v_____do__lift_1286_){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_nat_add(v_i_1281_, v___x_1287_);
v___x_1289_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1282_, v_f_1283_, v_keys_1284_, v_vals_1285_, v___x_1288_, v_____do__lift_1286_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse(lean_object* v_m_1290_, lean_object* v_inst_1291_, lean_object* v_00_u03c3_1292_, lean_object* v_00_u03b1_1293_, lean_object* v_00_u03b2_1294_, lean_object* v_f_1295_, lean_object* v_keys_1296_, lean_object* v_vals_1297_, lean_object* v_heq_1298_, lean_object* v_i_1299_, lean_object* v_acc_1300_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1291_, v_f_1295_, v_keys_1296_, v_vals_1297_, v_i_1299_, v_acc_1300_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object* v_inst_1302_, lean_object* v_f_1303_, lean_object* v_x_1304_, lean_object* v_x_1305_){
_start:
{
if (lean_obj_tag(v_x_1304_) == 0)
{
lean_object* v_toApplicative_1306_; lean_object* v_toPure_1307_; lean_object* v_es_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_toApplicative_1306_ = lean_ctor_get(v_inst_1302_, 0);
v_toPure_1307_ = lean_ctor_get(v_toApplicative_1306_, 1);
v_es_1308_ = lean_ctor_get(v_x_1304_, 0);
lean_inc_ref(v_es_1308_);
lean_dec_ref(v_x_1304_);
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = lean_array_get_size(v_es_1308_);
v___x_1311_ = lean_nat_dec_lt(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_inc(v_toPure_1307_);
lean_dec_ref(v_es_1308_);
lean_dec(v_f_1303_);
lean_dec_ref(v_inst_1302_);
v___x_1312_ = lean_apply_2(v_toPure_1307_, lean_box(0), v_x_1305_);
return v___x_1312_;
}
else
{
lean_object* v___f_1313_; uint8_t v___x_1314_; 
lean_inc(v_toPure_1307_);
lean_inc_ref(v_inst_1302_);
v___f_1313_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1313_, 0, v_f_1303_);
lean_closure_set(v___f_1313_, 1, v_inst_1302_);
lean_closure_set(v___f_1313_, 2, v_toPure_1307_);
v___x_1314_ = lean_nat_dec_le(v___x_1310_, v___x_1310_);
if (v___x_1314_ == 0)
{
if (v___x_1311_ == 0)
{
lean_object* v___x_1315_; 
lean_inc(v_toPure_1307_);
lean_dec_ref(v___f_1313_);
lean_dec_ref(v_es_1308_);
lean_dec_ref(v_inst_1302_);
v___x_1315_ = lean_apply_2(v_toPure_1307_, lean_box(0), v_x_1305_);
return v___x_1315_;
}
else
{
size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = ((size_t)0ULL);
v___x_1317_ = lean_usize_of_nat(v___x_1310_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1302_, v___f_1313_, v_es_1308_, v___x_1316_, v___x_1317_, v_x_1305_);
return v___x_1318_;
}
}
else
{
size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = lean_usize_of_nat(v___x_1310_);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1302_, v___f_1313_, v_es_1308_, v___x_1319_, v___x_1320_, v_x_1305_);
return v___x_1321_;
}
}
}
else
{
lean_object* v_ks_1322_; lean_object* v_vs_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_ks_1322_ = lean_ctor_get(v_x_1304_, 0);
lean_inc_ref(v_ks_1322_);
v_vs_1323_ = lean_ctor_get(v_x_1304_, 1);
lean_inc_ref(v_vs_1323_);
lean_dec_ref(v_x_1304_);
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1302_, v_f_1303_, v_ks_1322_, v_vs_1323_, v___x_1324_, v_x_1305_);
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0(lean_object* v_f_1326_, lean_object* v_inst_1327_, lean_object* v_toPure_1328_, lean_object* v_acc_1329_, lean_object* v_entry_1330_){
_start:
{
switch(lean_obj_tag(v_entry_1330_))
{
case 0:
{
lean_object* v_key_1331_; lean_object* v_val_1332_; lean_object* v___x_1333_; 
lean_dec(v_toPure_1328_);
lean_dec_ref(v_inst_1327_);
v_key_1331_ = lean_ctor_get(v_entry_1330_, 0);
lean_inc(v_key_1331_);
v_val_1332_ = lean_ctor_get(v_entry_1330_, 1);
lean_inc(v_val_1332_);
lean_dec_ref(v_entry_1330_);
v___x_1333_ = lean_apply_3(v_f_1326_, v_acc_1329_, v_key_1331_, v_val_1332_);
return v___x_1333_;
}
case 1:
{
lean_object* v_node_1334_; lean_object* v___x_1335_; 
lean_dec(v_toPure_1328_);
v_node_1334_ = lean_ctor_get(v_entry_1330_, 0);
lean_inc(v_node_1334_);
lean_dec_ref(v_entry_1330_);
v___x_1335_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1327_, v_f_1326_, v_node_1334_, v_acc_1329_);
return v___x_1335_;
}
default: 
{
lean_object* v___x_1336_; 
lean_dec_ref(v_inst_1327_);
lean_dec(v_f_1326_);
v___x_1336_ = lean_apply_2(v_toPure_1328_, lean_box(0), v_acc_1329_);
return v___x_1336_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux(lean_object* v_m_1337_, lean_object* v_inst_1338_, lean_object* v_00_u03c3_1339_, lean_object* v_00_u03b1_1340_, lean_object* v_00_u03b2_1341_, lean_object* v_f_1342_, lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1338_, v_f_1342_, v_x_1343_, v_x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___redArg(lean_object* v_inst_1346_, lean_object* v_map_1347_, lean_object* v_f_1348_, lean_object* v_init_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1346_, v_f_1348_, v_map_1347_, v_init_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM(lean_object* v_m_1351_, lean_object* v_inst_1352_, lean_object* v_00_u03c3_1353_, lean_object* v_00_u03b1_1354_, lean_object* v_00_u03b2_1355_, lean_object* v_x_1356_, lean_object* v_x_1357_, lean_object* v_map_1358_, lean_object* v_f_1359_, lean_object* v_init_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1352_, v_f_1359_, v_map_1358_, v_init_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___boxed(lean_object* v_m_1362_, lean_object* v_inst_1363_, lean_object* v_00_u03c3_1364_, lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_x_1367_, lean_object* v_x_1368_, lean_object* v_map_1369_, lean_object* v_f_1370_, lean_object* v_init_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_PersistentHashMap_foldlM(v_m_1362_, v_inst_1363_, v_00_u03c3_1364_, v_00_u03b1_1365_, v_00_u03b2_1366_, v_x_1367_, v_x_1368_, v_map_1369_, v_f_1370_, v_init_1371_);
lean_dec_ref(v_x_1368_);
lean_dec_ref(v_x_1367_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg___lam__0(lean_object* v_f_1373_, lean_object* v_x_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_apply_2(v_f_1373_, v___y_1375_, v___y_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg(lean_object* v_inst_1378_, lean_object* v_map_1379_, lean_object* v_f_1380_){
_start:
{
lean_object* v___f_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___f_1381_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1381_, 0, v_f_1380_);
v___x_1382_ = lean_box(0);
v___x_1383_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1378_, v___f_1381_, v_map_1379_, v___x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM(lean_object* v_m_1384_, lean_object* v_inst_1385_, lean_object* v_00_u03b1_1386_, lean_object* v_00_u03b2_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_, lean_object* v_map_1390_, lean_object* v_f_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_1385_, v_map_1390_, v_f_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___boxed(lean_object* v_m_1393_, lean_object* v_inst_1394_, lean_object* v_00_u03b1_1395_, lean_object* v_00_u03b2_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v_map_1399_, lean_object* v_f_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_PersistentHashMap_forM(v_m_1393_, v_inst_1394_, v_00_u03b1_1395_, v_00_u03b2_1396_, v_x_1397_, v_x_1398_, v_map_1399_, v_f_1400_);
lean_dec_ref(v_x_1398_);
lean_dec_ref(v_x_1397_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg___lam__0(lean_object* v_f_1402_, lean_object* v_x1_1403_, lean_object* v_x2_1404_, lean_object* v_x3_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_apply_3(v_f_1402_, v_x1_1403_, v_x2_1404_, v_x3_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object* v_map_1426_, lean_object* v_f_1427_, lean_object* v_init_1428_){
_start:
{
lean_object* v___f_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___f_1429_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1429_, 0, v_f_1427_);
v___x_1430_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1431_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1430_, v___f_1429_, v_map_1426_, v_init_1428_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl(lean_object* v_00_u03c3_1432_, lean_object* v_00_u03b1_1433_, lean_object* v_00_u03b2_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_map_1437_, lean_object* v_f_1438_, lean_object* v_init_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_1437_, v_f_1438_, v_init_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___boxed(lean_object* v_00_u03c3_1441_, lean_object* v_00_u03b1_1442_, lean_object* v_00_u03b2_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v_map_1446_, lean_object* v_f_1447_, lean_object* v_init_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_PersistentHashMap_foldl(v_00_u03c3_1441_, v_00_u03b1_1442_, v_00_u03b2_1443_, v_x_1444_, v_x_1445_, v_map_1446_, v_f_1447_, v_init_1448_);
lean_dec_ref(v_x_1445_);
lean_dec_ref(v_x_1444_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__0(lean_object* v_x_1450_){
_start:
{
if (lean_obj_tag(v_x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_a_1451_ = lean_ctor_get(v_x_1450_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v_x_1450_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v_x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_a_1459_ = lean_ctor_get(v_x_1450_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_x_1450_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v_x_1450_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v_x_1450_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__1(lean_object* v_toPure_1467_, lean_object* v_result_1468_){
_start:
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_ctor_get(v_result_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v_result_1468_);
v___x_1470_ = lean_apply_2(v_toPure_1467_, lean_box(0), v_a_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__2(lean_object* v_toFunctor_1471_, lean_object* v_f_1472_, lean_object* v_intoError_1473_, lean_object* v_s_1474_, lean_object* v_a_1475_, lean_object* v_b_1476_){
_start:
{
lean_object* v_map_1477_; lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1486_; 
v_map_1477_ = lean_ctor_get(v_toFunctor_1471_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_toFunctor_1471_);
if (v_isSharedCheck_1486_ == 0)
{
lean_object* v_unused_1487_; 
v_unused_1487_ = lean_ctor_get(v_toFunctor_1471_, 1);
lean_dec(v_unused_1487_);
v___x_1479_ = v_toFunctor_1471_;
v_isShared_1480_ = v_isSharedCheck_1486_;
goto v_resetjp_1478_;
}
else
{
lean_inc(v_map_1477_);
lean_dec(v_toFunctor_1471_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1486_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 1, v_b_1476_);
lean_ctor_set(v___x_1479_, 0, v_a_1475_);
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1475_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_b_1476_);
v___x_1482_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_apply_2(v_f_1472_, v___x_1482_, v_s_1474_);
v___x_1484_ = lean_apply_4(v_map_1477_, lean_box(0), lean_box(0), v_intoError_1473_, v___x_1483_);
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg(lean_object* v_inst_1489_, lean_object* v_map_1490_, lean_object* v_init_1491_, lean_object* v_f_1492_){
_start:
{
lean_object* v_toApplicative_1493_; lean_object* v_toBind_1494_; lean_object* v___f_1495_; lean_object* v___f_1496_; lean_object* v___f_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v_toFunctor_1505_; lean_object* v_toPure_1506_; lean_object* v_intoError_1507_; lean_object* v___f_1508_; lean_object* v___f_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v_toApplicative_1493_ = lean_ctor_get(v_inst_1489_, 0);
lean_inc_ref(v_toApplicative_1493_);
v_toBind_1494_ = lean_ctor_get(v_inst_1489_, 1);
lean_inc(v_toBind_1494_);
lean_inc_ref(v_inst_1489_);
v___f_1495_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1495_, 0, v_inst_1489_);
lean_inc_ref(v_inst_1489_);
v___f_1496_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1496_, 0, v_inst_1489_);
lean_inc_ref(v_inst_1489_);
v___f_1497_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1497_, 0, v_inst_1489_);
lean_inc_ref(v_inst_1489_);
v___f_1498_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1498_, 0, v_inst_1489_);
lean_inc_ref(v_inst_1489_);
v___x_1499_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1499_, 0, lean_box(0));
lean_closure_set(v___x_1499_, 1, lean_box(0));
lean_closure_set(v___x_1499_, 2, v_inst_1489_);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v___f_1495_);
lean_inc_ref(v_inst_1489_);
v___x_1501_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1501_, 0, lean_box(0));
lean_closure_set(v___x_1501_, 1, lean_box(0));
lean_closure_set(v___x_1501_, 2, v_inst_1489_);
v___x_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1500_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
lean_ctor_set(v___x_1502_, 2, v___f_1496_);
lean_ctor_set(v___x_1502_, 3, v___f_1497_);
lean_ctor_set(v___x_1502_, 4, v___f_1498_);
v___x_1503_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1503_, 0, lean_box(0));
lean_closure_set(v___x_1503_, 1, lean_box(0));
lean_closure_set(v___x_1503_, 2, v_inst_1489_);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v_toFunctor_1505_ = lean_ctor_get(v_toApplicative_1493_, 0);
lean_inc_ref(v_toFunctor_1505_);
v_toPure_1506_ = lean_ctor_get(v_toApplicative_1493_, 1);
lean_inc(v_toPure_1506_);
lean_dec_ref(v_toApplicative_1493_);
v_intoError_1507_ = ((lean_object*)(l_Lean_PersistentHashMap_forIn___redArg___closed__0));
v___f_1508_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1508_, 0, v_toPure_1506_);
v___f_1509_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__2), 6, 3);
lean_closure_set(v___f_1509_, 0, v_toFunctor_1505_);
lean_closure_set(v___f_1509_, 1, v_f_1492_);
lean_closure_set(v___f_1509_, 2, v_intoError_1507_);
v___x_1510_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1504_, v___f_1509_, v_map_1490_, v_init_1491_);
v___x_1511_ = lean_apply_4(v_toBind_1494_, lean_box(0), lean_box(0), v___x_1510_, v___f_1508_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn(lean_object* v_m_1512_, lean_object* v_00_u03c3_1513_, lean_object* v_00_u03b1_1514_, lean_object* v_00_u03b2_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_, lean_object* v_inst_1518_, lean_object* v_map_1519_, lean_object* v_init_1520_, lean_object* v_f_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1518_, v_map_1519_, v_init_1520_, v_f_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___boxed(lean_object* v_m_1523_, lean_object* v_00_u03c3_1524_, lean_object* v_00_u03b1_1525_, lean_object* v_00_u03b2_1526_, lean_object* v_x_1527_, lean_object* v_x_1528_, lean_object* v_inst_1529_, lean_object* v_map_1530_, lean_object* v_init_1531_, lean_object* v_f_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Lean_PersistentHashMap_forIn(v_m_1523_, v_00_u03c3_1524_, v_00_u03b1_1525_, v_00_u03b2_1526_, v_x_1527_, v_x_1528_, v_inst_1529_, v_map_1530_, v_init_1531_, v_f_1532_);
lean_dec_ref(v_x_1528_);
lean_dec_ref(v_x_1527_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_inst_1534_, lean_object* v_00_u03b2_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1534_, v___y_1536_, v___y_1537_, v___y_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1540_){
_start:
{
lean_object* v___f_1541_; 
v___f_1541_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1541_, 0, v_inst_1540_);
return v___f_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad(lean_object* v_m_1542_, lean_object* v_00_u03b1_1543_, lean_object* v_00_u03b2_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_, lean_object* v_inst_1547_){
_start:
{
lean_object* v___f_1548_; 
v___f_1548_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1548_, 0, v_inst_1547_);
return v___f_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___boxed(lean_object* v_m_1549_, lean_object* v_00_u03b1_1550_, lean_object* v_00_u03b2_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_, lean_object* v_inst_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_PersistentHashMap_instForInProdOfMonad(v_m_1549_, v_00_u03b1_1550_, v_00_u03b2_1551_, v_x_1552_, v_x_1553_, v_inst_1554_);
lean_dec_ref(v_x_1553_);
lean_dec_ref(v_x_1552_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__0(lean_object* v_toPure_1556_, lean_object* v_entries_x27_1557_){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_entries_x27_1557_);
v___x_1559_ = lean_apply_2(v_toPure_1556_, lean_box(0), v___x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__1(lean_object* v_toPure_1560_, lean_object* v_____do__lift_1561_){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1562_, 0, v_____do__lift_1561_);
v___x_1563_ = lean_apply_2(v_toPure_1560_, lean_box(0), v___x_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__2(lean_object* v_key_1564_, lean_object* v_toPure_1565_, lean_object* v_____do__lift_1566_){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_key_1564_);
lean_ctor_set(v___x_1567_, 1, v_____do__lift_1566_);
v___x_1568_ = lean_apply_2(v_toPure_1565_, lean_box(0), v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__4(lean_object* v_ks_1569_, lean_object* v_toPure_1570_, lean_object* v_____x_1571_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_ks_1569_);
lean_ctor_set(v___x_1572_, 1, v_____x_1571_);
v___x_1573_ = lean_apply_2(v_toPure_1570_, lean_box(0), v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg(lean_object* v_inst_1574_, lean_object* v_f_1575_, lean_object* v_n_1576_){
_start:
{
if (lean_obj_tag(v_n_1576_) == 0)
{
lean_object* v_toApplicative_1577_; lean_object* v_toBind_1578_; lean_object* v_toPure_1579_; lean_object* v_es_1580_; lean_object* v___f_1581_; lean_object* v___f_1582_; lean_object* v___f_1583_; size_t v_sz_1584_; size_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
v_toApplicative_1577_ = lean_ctor_get(v_inst_1574_, 0);
v_toBind_1578_ = lean_ctor_get(v_inst_1574_, 1);
lean_inc(v_toBind_1578_);
v_toPure_1579_ = lean_ctor_get(v_toApplicative_1577_, 1);
v_es_1580_ = lean_ctor_get(v_n_1576_, 0);
lean_inc_ref(v_es_1580_);
lean_dec_ref(v_n_1576_);
lean_inc(v_toPure_1579_);
v___f_1581_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1581_, 0, v_toPure_1579_);
lean_inc(v_toPure_1579_);
v___f_1582_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1582_, 0, v_toPure_1579_);
lean_inc_ref(v_inst_1574_);
lean_inc(v_toBind_1578_);
lean_inc(v_toPure_1579_);
v___f_1583_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1583_, 0, v_toPure_1579_);
lean_closure_set(v___f_1583_, 1, v_f_1575_);
lean_closure_set(v___f_1583_, 2, v_toBind_1578_);
lean_closure_set(v___f_1583_, 3, v_inst_1574_);
lean_closure_set(v___f_1583_, 4, v___f_1582_);
v_sz_1584_ = lean_array_size(v_es_1580_);
v___x_1585_ = ((size_t)0ULL);
v___x_1586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1574_, v___f_1583_, v_sz_1584_, v___x_1585_, v_es_1580_);
v___x_1587_ = lean_apply_4(v_toBind_1578_, lean_box(0), lean_box(0), v___x_1586_, v___f_1581_);
return v___x_1587_;
}
else
{
lean_object* v_toApplicative_1588_; lean_object* v_toBind_1589_; lean_object* v_toPure_1590_; lean_object* v_ks_1591_; lean_object* v_vs_1592_; lean_object* v___f_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v_toApplicative_1588_ = lean_ctor_get(v_inst_1574_, 0);
v_toBind_1589_ = lean_ctor_get(v_inst_1574_, 1);
lean_inc(v_toBind_1589_);
v_toPure_1590_ = lean_ctor_get(v_toApplicative_1588_, 1);
v_ks_1591_ = lean_ctor_get(v_n_1576_, 0);
lean_inc_ref(v_ks_1591_);
v_vs_1592_ = lean_ctor_get(v_n_1576_, 1);
lean_inc_ref(v_vs_1592_);
lean_dec_ref(v_n_1576_);
lean_inc(v_toPure_1590_);
v___f_1593_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__4), 3, 2);
lean_closure_set(v___f_1593_, 0, v_ks_1591_);
lean_closure_set(v___f_1593_, 1, v_toPure_1590_);
v___x_1594_ = l_Array_mapM_x27___redArg(v_inst_1574_, v_f_1575_, v_vs_1592_);
v___x_1595_ = lean_apply_4(v_toBind_1589_, lean_box(0), lean_box(0), v___x_1594_, v___f_1593_);
return v___x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__3(lean_object* v_toPure_1596_, lean_object* v_f_1597_, lean_object* v_toBind_1598_, lean_object* v_inst_1599_, lean_object* v___f_1600_, lean_object* v_x_1601_){
_start:
{
switch(lean_obj_tag(v_x_1601_))
{
case 0:
{
lean_object* v_key_1602_; lean_object* v_val_1603_; lean_object* v___f_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
lean_dec(v___f_1600_);
lean_dec_ref(v_inst_1599_);
v_key_1602_ = lean_ctor_get(v_x_1601_, 0);
lean_inc(v_key_1602_);
v_val_1603_ = lean_ctor_get(v_x_1601_, 1);
lean_inc(v_val_1603_);
lean_dec_ref(v_x_1601_);
v___f_1604_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1604_, 0, v_key_1602_);
lean_closure_set(v___f_1604_, 1, v_toPure_1596_);
v___x_1605_ = lean_apply_1(v_f_1597_, v_val_1603_);
v___x_1606_ = lean_apply_4(v_toBind_1598_, lean_box(0), lean_box(0), v___x_1605_, v___f_1604_);
return v___x_1606_;
}
case 1:
{
lean_object* v_node_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec(v_toPure_1596_);
v_node_1607_ = lean_ctor_get(v_x_1601_, 0);
lean_inc(v_node_1607_);
lean_dec_ref(v_x_1601_);
v___x_1608_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1599_, v_f_1597_, v_node_1607_);
v___x_1609_ = lean_apply_4(v_toBind_1598_, lean_box(0), lean_box(0), v___x_1608_, v___f_1600_);
return v___x_1609_;
}
default: 
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
lean_dec(v___f_1600_);
lean_dec_ref(v_inst_1599_);
lean_dec(v_toBind_1598_);
lean_dec(v_f_1597_);
v___x_1610_ = lean_box(2);
v___x_1611_ = lean_apply_2(v_toPure_1596_, lean_box(0), v___x_1610_);
return v___x_1611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux(lean_object* v_00_u03b1_1612_, lean_object* v_00_u03b2_1613_, lean_object* v_00_u03c3_1614_, lean_object* v_m_1615_, lean_object* v_inst_1616_, lean_object* v_f_1617_, lean_object* v_n_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1616_, v_f_1617_, v_n_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg___lam__0(lean_object* v_toPure_1620_, lean_object* v_root_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = lean_apply_2(v_toPure_1620_, lean_box(0), v_root_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object* v_inst_1623_, lean_object* v_pm_1624_, lean_object* v_f_1625_){
_start:
{
lean_object* v_toApplicative_1626_; lean_object* v_toBind_1627_; lean_object* v_toPure_1628_; lean_object* v___x_1629_; lean_object* v___f_1630_; lean_object* v___x_1631_; 
v_toApplicative_1626_ = lean_ctor_get(v_inst_1623_, 0);
v_toBind_1627_ = lean_ctor_get(v_inst_1623_, 1);
lean_inc(v_toBind_1627_);
v_toPure_1628_ = lean_ctor_get(v_toApplicative_1626_, 1);
lean_inc(v_toPure_1628_);
v___x_1629_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1623_, v_f_1625_, v_pm_1624_);
v___f_1630_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1630_, 0, v_toPure_1628_);
v___x_1631_ = lean_apply_4(v_toBind_1627_, lean_box(0), lean_box(0), v___x_1629_, v___f_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM(lean_object* v_00_u03b1_1632_, lean_object* v_00_u03b2_1633_, lean_object* v_00_u03c3_1634_, lean_object* v_m_1635_, lean_object* v_inst_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_pm_1639_, lean_object* v_f_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_1636_, v_pm_1639_, v_f_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___boxed(lean_object* v_00_u03b1_1642_, lean_object* v_00_u03b2_1643_, lean_object* v_00_u03c3_1644_, lean_object* v_m_1645_, lean_object* v_inst_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_, lean_object* v_pm_1649_, lean_object* v_f_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_PersistentHashMap_mapM(v_00_u03b1_1642_, v_00_u03b2_1643_, v_00_u03c3_1644_, v_m_1645_, v_inst_1646_, v_x_1647_, v_x_1648_, v_pm_1649_, v_f_1650_);
lean_dec_ref(v_x_1648_);
lean_dec_ref(v_x_1647_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg___lam__0(lean_object* v_f_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_apply_1(v_f_1652_, v_x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg(lean_object* v_pm_1655_, lean_object* v_f_1656_){
_start:
{
lean_object* v___f_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___f_1657_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1657_, 0, v_f_1656_);
v___x_1658_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1659_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_1658_, v_pm_1655_, v___f_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map(lean_object* v_00_u03b1_1660_, lean_object* v_00_u03b2_1661_, lean_object* v_00_u03c3_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_, lean_object* v_pm_1665_, lean_object* v_f_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_PersistentHashMap_map___redArg(v_pm_1665_, v_f_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___boxed(lean_object* v_00_u03b1_1668_, lean_object* v_00_u03b2_1669_, lean_object* v_00_u03c3_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_, lean_object* v_pm_1673_, lean_object* v_f_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_PersistentHashMap_map(v_00_u03b1_1668_, v_00_u03b2_1669_, v_00_u03c3_1670_, v_x_1671_, v_x_1672_, v_pm_1673_, v_f_1674_);
lean_dec_ref(v_x_1672_);
lean_dec_ref(v_x_1671_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg___lam__0(lean_object* v_ps_1676_, lean_object* v_k_1677_, lean_object* v_v_1678_){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1679_, 0, v_k_1677_);
lean_ctor_set(v___x_1679_, 1, v_v_1678_);
v___x_1680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v_ps_1676_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg(lean_object* v_m_1682_){
_start:
{
lean_object* v___f_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___f_1683_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___redArg___closed__0));
v___x_1684_ = lean_box(0);
v___x_1685_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1682_, v___f_1683_, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList(lean_object* v_00_u03b1_1686_, lean_object* v_00_u03b2_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_, lean_object* v_m_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_PersistentHashMap_toList___redArg(v_m_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___boxed(lean_object* v_00_u03b1_1692_, lean_object* v_00_u03b2_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_, lean_object* v_m_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_PersistentHashMap_toList(v_00_u03b1_1692_, v_00_u03b2_1693_, v_x_1694_, v_x_1695_, v_m_1696_);
lean_dec_ref(v_x_1695_);
lean_dec_ref(v_x_1694_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg___lam__0(lean_object* v_ps_1698_, lean_object* v_k_1699_, lean_object* v_v_1700_){
_start:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_k_1699_);
lean_ctor_set(v___x_1701_, 1, v_v_1700_);
v___x_1702_ = lean_array_push(v_ps_1698_, v___x_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg(lean_object* v_m_1706_){
_start:
{
lean_object* v___f_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___f_1707_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__0));
v___x_1708_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__1));
v___x_1709_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1706_, v___f_1707_, v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray(lean_object* v_00_u03b1_1710_, lean_object* v_00_u03b2_1711_, lean_object* v_x_1712_, lean_object* v_x_1713_, lean_object* v_m_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_PersistentHashMap_toArray___redArg(v_m_1714_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___boxed(lean_object* v_00_u03b1_1716_, lean_object* v_00_u03b2_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v_m_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_PersistentHashMap_toArray(v_00_u03b1_1716_, v_00_u03b2_1717_, v_x_1718_, v_x_1719_, v_m_1720_);
lean_dec_ref(v_x_1719_);
lean_dec_ref(v_x_1718_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg(lean_object* v_x_1722_, lean_object* v_x_1723_, lean_object* v_x_1724_){
_start:
{
if (lean_obj_tag(v_x_1722_) == 0)
{
lean_object* v_es_1725_; lean_object* v_numNodes_1726_; lean_object* v_numNull_1727_; lean_object* v_numCollisions_1728_; lean_object* v_maxDepth_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1751_; 
v_es_1725_ = lean_ctor_get(v_x_1722_, 0);
v_numNodes_1726_ = lean_ctor_get(v_x_1723_, 0);
v_numNull_1727_ = lean_ctor_get(v_x_1723_, 1);
v_numCollisions_1728_ = lean_ctor_get(v_x_1723_, 2);
v_maxDepth_1729_ = lean_ctor_get(v_x_1723_, 3);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_x_1723_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1731_ = v_x_1723_;
v_isShared_1732_ = v_isSharedCheck_1751_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_maxDepth_1729_);
lean_inc(v_numCollisions_1728_);
lean_inc(v_numNull_1727_);
lean_inc(v_numNodes_1726_);
lean_dec(v_x_1723_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1751_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___y_1736_; uint8_t v___x_1750_; 
v___x_1733_ = lean_unsigned_to_nat(1u);
v___x_1734_ = lean_nat_add(v_numNodes_1726_, v___x_1733_);
lean_dec(v_numNodes_1726_);
v___x_1750_ = lean_nat_dec_le(v_maxDepth_1729_, v_x_1724_);
if (v___x_1750_ == 0)
{
v___y_1736_ = v_maxDepth_1729_;
goto v___jp_1735_;
}
else
{
lean_dec(v_maxDepth_1729_);
lean_inc(v_x_1724_);
v___y_1736_ = v_x_1724_;
goto v___jp_1735_;
}
v___jp_1735_:
{
lean_object* v_stats_1738_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 3, v___y_1736_);
lean_ctor_set(v___x_1731_, 0, v___x_1734_);
v_stats_1738_ = v___x_1731_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_numNull_1727_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v_numCollisions_1728_);
lean_ctor_set(v_reuseFailAlloc_1749_, 3, v___y_1736_);
v_stats_1738_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1739_ = lean_unsigned_to_nat(0u);
v___x_1740_ = lean_array_get_size(v_es_1725_);
v___x_1741_ = lean_nat_dec_lt(v___x_1739_, v___x_1740_);
if (v___x_1741_ == 0)
{
lean_dec(v_x_1724_);
return v_stats_1738_;
}
else
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_nat_dec_le(v___x_1740_, v___x_1740_);
if (v___x_1742_ == 0)
{
if (v___x_1741_ == 0)
{
lean_dec(v_x_1724_);
return v_stats_1738_;
}
else
{
size_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = ((size_t)0ULL);
v___x_1744_ = lean_usize_of_nat(v___x_1740_);
v___x_1745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1724_, v_es_1725_, v___x_1743_, v___x_1744_, v_stats_1738_);
lean_dec(v_x_1724_);
return v___x_1745_;
}
}
else
{
size_t v___x_1746_; size_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = ((size_t)0ULL);
v___x_1747_ = lean_usize_of_nat(v___x_1740_);
v___x_1748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1724_, v_es_1725_, v___x_1746_, v___x_1747_, v_stats_1738_);
lean_dec(v_x_1724_);
return v___x_1748_;
}
}
}
}
}
}
else
{
lean_object* v_ks_1752_; lean_object* v_numNodes_1753_; lean_object* v_numNull_1754_; lean_object* v_numCollisions_1755_; lean_object* v_maxDepth_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1772_; 
v_ks_1752_ = lean_ctor_get(v_x_1722_, 0);
v_numNodes_1753_ = lean_ctor_get(v_x_1723_, 0);
v_numNull_1754_ = lean_ctor_get(v_x_1723_, 1);
v_numCollisions_1755_ = lean_ctor_get(v_x_1723_, 2);
v_maxDepth_1756_ = lean_ctor_get(v_x_1723_, 3);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_x_1723_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1758_ = v_x_1723_;
v_isShared_1759_ = v_isSharedCheck_1772_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_maxDepth_1756_);
lean_inc(v_numCollisions_1755_);
lean_inc(v_numNull_1754_);
lean_inc(v_numNodes_1753_);
lean_dec(v_x_1723_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1772_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = lean_nat_add(v_numNodes_1753_, v___x_1760_);
lean_dec(v_numNodes_1753_);
v___x_1762_ = lean_array_get_size(v_ks_1752_);
v___x_1763_ = lean_nat_add(v_numCollisions_1755_, v___x_1762_);
lean_dec(v_numCollisions_1755_);
v___x_1764_ = lean_nat_sub(v___x_1763_, v___x_1760_);
lean_dec(v___x_1763_);
v___x_1765_ = lean_nat_dec_le(v_maxDepth_1756_, v_x_1724_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1767_; 
lean_dec(v_x_1724_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 2, v___x_1764_);
lean_ctor_set(v___x_1758_, 0, v___x_1761_);
v___x_1767_ = v___x_1758_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_numNull_1754_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_maxDepth_1756_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
else
{
lean_object* v___x_1770_; 
lean_dec(v_maxDepth_1756_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 3, v_x_1724_);
lean_ctor_set(v___x_1758_, 2, v___x_1764_);
lean_ctor_set(v___x_1758_, 0, v___x_1761_);
v___x_1770_ = v___x_1758_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_numNull_1754_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_x_1724_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(lean_object* v_x_1773_, lean_object* v_as_1774_, size_t v_i_1775_, size_t v_stop_1776_, lean_object* v_b_1777_){
_start:
{
lean_object* v___y_1779_; uint8_t v___x_1783_; 
v___x_1783_ = lean_usize_dec_eq(v_i_1775_, v_stop_1776_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_unsigned_to_nat(1u);
v___x_1785_ = lean_array_uget_borrowed(v_as_1774_, v_i_1775_);
switch(lean_obj_tag(v___x_1785_))
{
case 0:
{
v___y_1779_ = v_b_1777_;
goto v___jp_1778_;
}
case 1:
{
lean_object* v_node_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_node_1786_ = lean_ctor_get(v___x_1785_, 0);
v___x_1787_ = lean_nat_add(v_x_1773_, v___x_1784_);
v___x_1788_ = l_Lean_PersistentHashMap_collectStats___redArg(v_node_1786_, v_b_1777_, v___x_1787_);
v___y_1779_ = v___x_1788_;
goto v___jp_1778_;
}
default: 
{
lean_object* v_numNodes_1789_; lean_object* v_numNull_1790_; lean_object* v_numCollisions_1791_; lean_object* v_maxDepth_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1800_; 
v_numNodes_1789_ = lean_ctor_get(v_b_1777_, 0);
v_numNull_1790_ = lean_ctor_get(v_b_1777_, 1);
v_numCollisions_1791_ = lean_ctor_get(v_b_1777_, 2);
v_maxDepth_1792_ = lean_ctor_get(v_b_1777_, 3);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_b_1777_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1794_ = v_b_1777_;
v_isShared_1795_ = v_isSharedCheck_1800_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_maxDepth_1792_);
lean_inc(v_numCollisions_1791_);
lean_inc(v_numNull_1790_);
lean_inc(v_numNodes_1789_);
lean_dec(v_b_1777_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1800_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1796_ = lean_nat_add(v_numNull_1790_, v___x_1784_);
lean_dec(v_numNull_1790_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 1, v___x_1796_);
v___x_1798_ = v___x_1794_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_numNodes_1789_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_numCollisions_1791_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_maxDepth_1792_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
v___y_1779_ = v___x_1798_;
goto v___jp_1778_;
}
}
}
}
}
else
{
return v_b_1777_;
}
v___jp_1778_:
{
size_t v___x_1780_; size_t v___x_1781_; 
v___x_1780_ = ((size_t)1ULL);
v___x_1781_ = lean_usize_add(v_i_1775_, v___x_1780_);
v_i_1775_ = v___x_1781_;
v_b_1777_ = v___y_1779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg___boxed(lean_object* v_x_1801_, lean_object* v_as_1802_, lean_object* v_i_1803_, lean_object* v_stop_1804_, lean_object* v_b_1805_){
_start:
{
size_t v_i_boxed_1806_; size_t v_stop_boxed_1807_; lean_object* v_res_1808_; 
v_i_boxed_1806_ = lean_unbox_usize(v_i_1803_);
lean_dec(v_i_1803_);
v_stop_boxed_1807_ = lean_unbox_usize(v_stop_1804_);
lean_dec(v_stop_1804_);
v_res_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1801_, v_as_1802_, v_i_boxed_1806_, v_stop_boxed_1807_, v_b_1805_);
lean_dec_ref(v_as_1802_);
lean_dec(v_x_1801_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg___boxed(lean_object* v_x_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_1809_, v_x_1810_, v_x_1811_);
lean_dec_ref(v_x_1809_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats(lean_object* v_00_u03b1_1813_, lean_object* v_00_u03b2_1814_, lean_object* v_x_1815_, lean_object* v_x_1816_, lean_object* v_x_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_1815_, v_x_1816_, v_x_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_00_u03b2_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v_x_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_PersistentHashMap_collectStats(v_00_u03b1_1819_, v_00_u03b2_1820_, v_x_1821_, v_x_1822_, v_x_1823_);
lean_dec_ref(v_x_1821_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(lean_object* v_00_u03b1_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_x_1827_, lean_object* v_as_1828_, size_t v_i_1829_, size_t v_stop_1830_, lean_object* v_b_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1827_, v_as_1828_, v_i_1829_, v_stop_1830_, v_b_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___boxed(lean_object* v_00_u03b1_1833_, lean_object* v_00_u03b2_1834_, lean_object* v_x_1835_, lean_object* v_as_1836_, lean_object* v_i_1837_, lean_object* v_stop_1838_, lean_object* v_b_1839_){
_start:
{
size_t v_i_boxed_1840_; size_t v_stop_boxed_1841_; lean_object* v_res_1842_; 
v_i_boxed_1840_ = lean_unbox_usize(v_i_1837_);
lean_dec(v_i_1837_);
v_stop_boxed_1841_ = lean_unbox_usize(v_stop_1838_);
lean_dec(v_stop_1838_);
v_res_1842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(v_00_u03b1_1833_, v_00_u03b2_1834_, v_x_1835_, v_as_1836_, v_i_boxed_1840_, v_stop_boxed_1841_, v_b_1839_);
lean_dec_ref(v_as_1836_);
lean_dec(v_x_1835_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg(lean_object* v_m_1845_){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = ((lean_object*)(l_Lean_PersistentHashMap_stats___redArg___closed__0));
v___x_1847_ = lean_unsigned_to_nat(1u);
v___x_1848_ = l_Lean_PersistentHashMap_collectStats___redArg(v_m_1845_, v___x_1846_, v___x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg___boxed(lean_object* v_m_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_PersistentHashMap_stats___redArg(v_m_1849_);
lean_dec_ref(v_m_1849_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats(lean_object* v_00_u03b1_1851_, lean_object* v_00_u03b2_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v_m_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_PersistentHashMap_stats___redArg(v_m_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___boxed(lean_object* v_00_u03b1_1857_, lean_object* v_00_u03b2_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_, lean_object* v_m_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_PersistentHashMap_stats(v_00_u03b1_1857_, v_00_u03b2_1858_, v_x_1859_, v_x_1860_, v_m_1861_);
lean_dec_ref(v_m_1861_);
lean_dec_ref(v_x_1860_);
lean_dec_ref(v_x_1859_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Stats_toString(lean_object* v_s_1868_){
_start:
{
lean_object* v_numNodes_1869_; lean_object* v_numNull_1870_; lean_object* v_numCollisions_1871_; lean_object* v_maxDepth_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_numNodes_1869_ = lean_ctor_get(v_s_1868_, 0);
lean_inc(v_numNodes_1869_);
v_numNull_1870_ = lean_ctor_get(v_s_1868_, 1);
lean_inc(v_numNull_1870_);
v_numCollisions_1871_ = lean_ctor_get(v_s_1868_, 2);
lean_inc(v_numCollisions_1871_);
v_maxDepth_1872_ = lean_ctor_get(v_s_1868_, 3);
lean_inc(v_maxDepth_1872_);
lean_dec_ref(v_s_1868_);
v___x_1873_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__0));
v___x_1874_ = l_Nat_reprFast(v_numNodes_1869_);
v___x_1875_ = lean_string_append(v___x_1873_, v___x_1874_);
lean_dec_ref(v___x_1874_);
v___x_1876_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__1));
v___x_1877_ = lean_string_append(v___x_1875_, v___x_1876_);
v___x_1878_ = l_Nat_reprFast(v_numNull_1870_);
v___x_1879_ = lean_string_append(v___x_1877_, v___x_1878_);
lean_dec_ref(v___x_1878_);
v___x_1880_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__2));
v___x_1881_ = lean_string_append(v___x_1879_, v___x_1880_);
v___x_1882_ = l_Nat_reprFast(v_numCollisions_1871_);
v___x_1883_ = lean_string_append(v___x_1881_, v___x_1882_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__3));
v___x_1885_ = lean_string_append(v___x_1883_, v___x_1884_);
v___x_1886_ = l_Nat_reprFast(v_maxDepth_1872_);
v___x_1887_ = lean_string_append(v___x_1885_, v___x_1886_);
lean_dec_ref(v___x_1886_);
v___x_1888_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__4));
v___x_1889_ = lean_string_append(v___x_1887_, v___x_1888_);
return v___x_1889_;
}
}
lean_object* runtime_initialize_Init_Data_Array_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_Except(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
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
