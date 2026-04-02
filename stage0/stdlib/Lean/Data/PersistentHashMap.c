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
v_val_725_ = lean_ctor_get(v___x_722_, 0);
lean_inc(v_val_725_);
lean_dec_ref(v___x_722_);
return v_val_725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg___boxed(lean_object* v_x_726_, lean_object* v_x_727_, lean_object* v_inst_728_, lean_object* v_m_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_PersistentHashMap_find_x21___redArg(v_x_726_, v_x_727_, v_inst_728_, v_m_729_, v_a_730_);
lean_dec(v_inst_728_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21(lean_object* v_00_u03b1_732_, lean_object* v_00_u03b2_733_, lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_inst_736_, lean_object* v_m_737_, lean_object* v_a_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_734_, v_x_735_, v_m_737_, v_a_738_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_741_ = l_panic___redArg(v_inst_736_, v___x_740_);
return v___x_741_;
}
else
{
lean_object* v_val_742_; 
v_val_742_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_742_);
lean_dec_ref(v___x_739_);
return v_val_742_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___boxed(lean_object* v_00_u03b1_743_, lean_object* v_00_u03b2_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_inst_747_, lean_object* v_m_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lean_PersistentHashMap_find_x21(v_00_u03b1_743_, v_00_u03b2_744_, v_x_745_, v_x_746_, v_inst_747_, v_m_748_, v_a_749_);
lean_dec(v_inst_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg(lean_object* v_inst_751_, lean_object* v_keys_752_, lean_object* v_vals_753_, lean_object* v_i_754_, lean_object* v_k_755_){
_start:
{
lean_object* v___x_756_; uint8_t v___x_757_; 
v___x_756_ = lean_array_get_size(v_keys_752_);
v___x_757_ = lean_nat_dec_lt(v_i_754_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; 
lean_dec(v_k_755_);
lean_dec(v_i_754_);
lean_dec_ref(v_inst_751_);
v___x_758_ = lean_box(0);
return v___x_758_;
}
else
{
lean_object* v_k_x27_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_k_x27_759_ = lean_array_fget_borrowed(v_keys_752_, v_i_754_);
lean_inc_ref(v_inst_751_);
lean_inc(v_k_x27_759_);
lean_inc(v_k_755_);
v___x_760_ = lean_apply_2(v_inst_751_, v_k_755_, v_k_x27_759_);
v___x_761_ = lean_unbox(v___x_760_);
if (v___x_761_ == 0)
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_i_754_, v___x_762_);
lean_dec(v_i_754_);
v_i_754_ = v___x_763_;
goto _start;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_dec(v_k_755_);
lean_dec_ref(v_inst_751_);
v___x_765_ = lean_array_fget_borrowed(v_vals_753_, v_i_754_);
lean_dec(v_i_754_);
lean_inc(v___x_765_);
lean_inc(v_k_x27_759_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_k_x27_759_);
lean_ctor_set(v___x_766_, 1, v___x_765_);
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg___boxed(lean_object* v_inst_768_, lean_object* v_keys_769_, lean_object* v_vals_770_, lean_object* v_i_771_, lean_object* v_k_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_768_, v_keys_769_, v_vals_770_, v_i_771_, v_k_772_);
lean_dec_ref(v_vals_770_);
lean_dec_ref(v_keys_769_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux(lean_object* v_00_u03b1_774_, lean_object* v_00_u03b2_775_, lean_object* v_inst_776_, lean_object* v_keys_777_, lean_object* v_vals_778_, lean_object* v_heq_779_, lean_object* v_i_780_, lean_object* v_k_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_776_, v_keys_777_, v_vals_778_, v_i_780_, v_k_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___boxed(lean_object* v_00_u03b1_783_, lean_object* v_00_u03b2_784_, lean_object* v_inst_785_, lean_object* v_keys_786_, lean_object* v_vals_787_, lean_object* v_heq_788_, lean_object* v_i_789_, lean_object* v_k_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_PersistentHashMap_findEntryAtAux(v_00_u03b1_783_, v_00_u03b2_784_, v_inst_785_, v_keys_786_, v_vals_787_, v_heq_788_, v_i_789_, v_k_790_);
lean_dec_ref(v_vals_787_);
lean_dec_ref(v_keys_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg(lean_object* v_inst_792_, lean_object* v_x_793_, size_t v_x_794_, lean_object* v_x_795_){
_start:
{
if (lean_obj_tag(v_x_793_) == 0)
{
lean_object* v_es_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_825_; 
v_es_796_ = lean_ctor_get(v_x_793_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v_x_793_);
if (v_isSharedCheck_825_ == 0)
{
v___x_798_ = v_x_793_;
v_isShared_799_ = v_isSharedCheck_825_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_es_796_);
lean_dec(v_x_793_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_825_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; size_t v___x_801_; size_t v___x_802_; size_t v___x_803_; lean_object* v_j_804_; lean_object* v___x_805_; 
v___x_800_ = lean_box(2);
v___x_801_ = ((size_t)5ULL);
v___x_802_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_803_ = lean_usize_land(v_x_794_, v___x_802_);
v_j_804_ = lean_usize_to_nat(v___x_803_);
v___x_805_ = lean_array_get(v___x_800_, v_es_796_, v_j_804_);
lean_dec(v_j_804_);
lean_dec_ref(v_es_796_);
switch(lean_obj_tag(v___x_805_))
{
case 0:
{
lean_object* v_key_806_; lean_object* v_val_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_820_; 
v_key_806_ = lean_ctor_get(v___x_805_, 0);
v_val_807_ = lean_ctor_get(v___x_805_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_820_ == 0)
{
v___x_809_ = v___x_805_;
v_isShared_810_ = v_isSharedCheck_820_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_val_807_);
lean_inc(v_key_806_);
lean_dec(v___x_805_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_820_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; uint8_t v___x_812_; 
lean_inc(v_key_806_);
v___x_811_ = lean_apply_2(v_inst_792_, v_x_795_, v_key_806_);
v___x_812_ = lean_unbox(v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_del_object(v___x_809_);
lean_dec(v_val_807_);
lean_dec(v_key_806_);
lean_del_object(v___x_798_);
v___x_813_ = lean_box(0);
return v___x_813_;
}
else
{
lean_object* v___x_815_; 
if (v_isShared_810_ == 0)
{
v___x_815_ = v___x_809_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v_key_806_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_val_807_);
v___x_815_ = v_reuseFailAlloc_819_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 1);
lean_ctor_set(v___x_798_, 0, v___x_815_);
v___x_817_ = v___x_798_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_815_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
case 1:
{
lean_object* v_node_821_; size_t v___x_822_; 
lean_del_object(v___x_798_);
v_node_821_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_node_821_);
lean_dec_ref(v___x_805_);
v___x_822_ = lean_usize_shift_right(v_x_794_, v___x_801_);
v_x_793_ = v_node_821_;
v_x_794_ = v___x_822_;
goto _start;
}
default: 
{
lean_object* v___x_824_; 
lean_del_object(v___x_798_);
lean_dec(v_x_795_);
lean_dec_ref(v_inst_792_);
v___x_824_ = lean_box(0);
return v___x_824_;
}
}
}
}
else
{
lean_object* v_ks_826_; lean_object* v_vs_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_ks_826_ = lean_ctor_get(v_x_793_, 0);
lean_inc_ref(v_ks_826_);
v_vs_827_ = lean_ctor_get(v_x_793_, 1);
lean_inc_ref(v_vs_827_);
lean_dec_ref(v_x_793_);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_792_, v_ks_826_, v_vs_827_, v___x_828_, v_x_795_);
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
v___x_842_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_838_, v_x_839_, v_x_840_, v_x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___boxed(lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_inst_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
size_t v_x_235__boxed_849_; lean_object* v_res_850_; 
v_x_235__boxed_849_ = lean_unbox_usize(v_x_847_);
lean_dec(v_x_847_);
v_res_850_ = l_Lean_PersistentHashMap_findEntryAux(v_00_u03b1_843_, v_00_u03b2_844_, v_inst_845_, v_x_846_, v_x_235__boxed_849_, v_x_848_);
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
v___x_858_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_x_851_, v_x_853_, v___x_857_, v_x_854_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f(lean_object* v_00_u03b1_859_, lean_object* v_00_u03b2_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_861_, v_x_862_, v_x_863_, v_x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg(lean_object* v_inst_866_, lean_object* v_keys_867_, lean_object* v_i_868_, lean_object* v_k_869_, lean_object* v_k_u2080_870_){
_start:
{
lean_object* v___x_871_; uint8_t v___x_872_; 
v___x_871_ = lean_array_get_size(v_keys_867_);
v___x_872_ = lean_nat_dec_lt(v_i_868_, v___x_871_);
if (v___x_872_ == 0)
{
lean_dec(v_k_869_);
lean_dec(v_i_868_);
lean_dec_ref(v_inst_866_);
lean_inc(v_k_u2080_870_);
return v_k_u2080_870_;
}
else
{
lean_object* v_k_x27_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_k_x27_873_ = lean_array_fget_borrowed(v_keys_867_, v_i_868_);
lean_inc_ref(v_inst_866_);
lean_inc(v_k_x27_873_);
lean_inc(v_k_869_);
v___x_874_ = lean_apply_2(v_inst_866_, v_k_869_, v_k_x27_873_);
v___x_875_ = lean_unbox(v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = lean_unsigned_to_nat(1u);
v___x_877_ = lean_nat_add(v_i_868_, v___x_876_);
lean_dec(v_i_868_);
v_i_868_ = v___x_877_;
goto _start;
}
else
{
lean_dec(v_k_869_);
lean_dec(v_i_868_);
lean_dec_ref(v_inst_866_);
lean_inc(v_k_x27_873_);
return v_k_x27_873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg___boxed(lean_object* v_inst_879_, lean_object* v_keys_880_, lean_object* v_i_881_, lean_object* v_k_882_, lean_object* v_k_u2080_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_879_, v_keys_880_, v_i_881_, v_k_882_, v_k_u2080_883_);
lean_dec(v_k_u2080_883_);
lean_dec_ref(v_keys_880_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux(lean_object* v_00_u03b1_885_, lean_object* v_00_u03b2_886_, lean_object* v_inst_887_, lean_object* v_keys_888_, lean_object* v_vals_889_, lean_object* v_heq_890_, lean_object* v_i_891_, lean_object* v_k_892_, lean_object* v_k_u2080_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_887_, v_keys_888_, v_i_891_, v_k_892_, v_k_u2080_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___boxed(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_inst_897_, lean_object* v_keys_898_, lean_object* v_vals_899_, lean_object* v_heq_900_, lean_object* v_i_901_, lean_object* v_k_902_, lean_object* v_k_u2080_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_PersistentHashMap_findKeyDAtAux(v_00_u03b1_895_, v_00_u03b2_896_, v_inst_897_, v_keys_898_, v_vals_899_, v_heq_900_, v_i_901_, v_k_902_, v_k_u2080_903_);
lean_dec(v_k_u2080_903_);
lean_dec_ref(v_vals_899_);
lean_dec_ref(v_keys_898_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object* v_inst_905_, lean_object* v_x_906_, size_t v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_){
_start:
{
if (lean_obj_tag(v_x_906_) == 0)
{
lean_object* v_es_910_; lean_object* v___x_911_; size_t v___x_912_; size_t v___x_913_; size_t v___x_914_; lean_object* v_j_915_; lean_object* v___x_916_; 
v_es_910_ = lean_ctor_get(v_x_906_, 0);
lean_inc_ref(v_es_910_);
lean_dec_ref(v_x_906_);
v___x_911_ = lean_box(2);
v___x_912_ = ((size_t)5ULL);
v___x_913_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_914_ = lean_usize_land(v_x_907_, v___x_913_);
v_j_915_ = lean_usize_to_nat(v___x_914_);
v___x_916_ = lean_array_get(v___x_911_, v_es_910_, v_j_915_);
lean_dec(v_j_915_);
lean_dec_ref(v_es_910_);
switch(lean_obj_tag(v___x_916_))
{
case 0:
{
lean_object* v_key_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_key_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc_n(v_key_917_, 2);
lean_dec_ref(v___x_916_);
v___x_918_ = lean_apply_2(v_inst_905_, v_x_908_, v_key_917_);
v___x_919_ = lean_unbox(v___x_918_);
if (v___x_919_ == 0)
{
lean_dec(v_key_917_);
lean_inc(v_x_909_);
return v_x_909_;
}
else
{
return v_key_917_;
}
}
case 1:
{
lean_object* v_node_920_; size_t v___x_921_; 
v_node_920_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_node_920_);
lean_dec_ref(v___x_916_);
v___x_921_ = lean_usize_shift_right(v_x_907_, v___x_912_);
v_x_906_ = v_node_920_;
v_x_907_ = v___x_921_;
goto _start;
}
default: 
{
lean_dec(v_x_908_);
lean_dec_ref(v_inst_905_);
lean_inc(v_x_909_);
return v_x_909_;
}
}
}
else
{
lean_object* v_ks_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_ks_923_ = lean_ctor_get(v_x_906_, 0);
lean_inc_ref(v_ks_923_);
lean_dec_ref(v_x_906_);
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_905_, v_ks_923_, v___x_924_, v_x_908_, v_x_909_);
lean_dec_ref(v_ks_923_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg___boxed(lean_object* v_inst_926_, lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v_x_930_){
_start:
{
size_t v_x_140__boxed_931_; lean_object* v_res_932_; 
v_x_140__boxed_931_ = lean_unbox_usize(v_x_928_);
lean_dec(v_x_928_);
v_res_932_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_926_, v_x_927_, v_x_140__boxed_931_, v_x_929_, v_x_930_);
lean_dec(v_x_930_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux(lean_object* v_00_u03b1_933_, lean_object* v_00_u03b2_934_, lean_object* v_inst_935_, lean_object* v_x_936_, size_t v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_935_, v_x_936_, v_x_937_, v_x_938_, v_x_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___boxed(lean_object* v_00_u03b1_941_, lean_object* v_00_u03b2_942_, lean_object* v_inst_943_, lean_object* v_x_944_, lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
size_t v_x_189__boxed_948_; lean_object* v_res_949_; 
v_x_189__boxed_948_ = lean_unbox_usize(v_x_945_);
lean_dec(v_x_945_);
v_res_949_ = l_Lean_PersistentHashMap_findKeyDAux(v_00_u03b1_941_, v_00_u03b2_942_, v_inst_943_, v_x_944_, v_x_189__boxed_948_, v_x_946_, v_x_947_);
lean_dec(v_x_947_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg(lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_m_952_, lean_object* v_a_953_, lean_object* v_a_u2080_954_){
_start:
{
lean_object* v___x_955_; uint64_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
lean_inc(v_a_953_);
v___x_955_ = lean_apply_1(v_x_951_, v_a_953_);
v___x_956_ = lean_unbox_uint64(v___x_955_);
lean_dec_ref(v___x_955_);
v___x_957_ = lean_uint64_to_usize(v___x_956_);
v___x_958_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_950_, v_m_952_, v___x_957_, v_a_953_, v_a_u2080_954_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg___boxed(lean_object* v_x_959_, lean_object* v_x_960_, lean_object* v_m_961_, lean_object* v_a_962_, lean_object* v_a_u2080_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_PersistentHashMap_findKeyD___redArg(v_x_959_, v_x_960_, v_m_961_, v_a_962_, v_a_u2080_963_);
lean_dec(v_a_u2080_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD(lean_object* v_00_u03b1_965_, lean_object* v_00_u03b2_966_, lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v_m_969_, lean_object* v_a_970_, lean_object* v_a_u2080_971_){
_start:
{
lean_object* v___x_972_; uint64_t v___x_973_; size_t v___x_974_; lean_object* v___x_975_; 
lean_inc(v_a_970_);
v___x_972_ = lean_apply_1(v_x_968_, v_a_970_);
v___x_973_ = lean_unbox_uint64(v___x_972_);
lean_dec_ref(v___x_972_);
v___x_974_ = lean_uint64_to_usize(v___x_973_);
v___x_975_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_967_, v_m_969_, v___x_974_, v_a_970_, v_a_u2080_971_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___boxed(lean_object* v_00_u03b1_976_, lean_object* v_00_u03b2_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_m_980_, lean_object* v_a_981_, lean_object* v_a_u2080_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_PersistentHashMap_findKeyD(v_00_u03b1_976_, v_00_u03b2_977_, v_x_978_, v_x_979_, v_m_980_, v_a_981_, v_a_u2080_982_);
lean_dec(v_a_u2080_982_);
return v_res_983_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___redArg(lean_object* v_inst_984_, lean_object* v_keys_985_, lean_object* v_i_986_, lean_object* v_k_987_){
_start:
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = lean_array_get_size(v_keys_985_);
v___x_989_ = lean_nat_dec_lt(v_i_986_, v___x_988_);
if (v___x_989_ == 0)
{
lean_dec(v_k_987_);
lean_dec(v_i_986_);
lean_dec_ref(v_inst_984_);
return v___x_989_;
}
else
{
lean_object* v_k_x27_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_k_x27_990_ = lean_array_fget_borrowed(v_keys_985_, v_i_986_);
lean_inc_ref(v_inst_984_);
lean_inc(v_k_x27_990_);
lean_inc(v_k_987_);
v___x_991_ = lean_apply_2(v_inst_984_, v_k_987_, v_k_x27_990_);
v___x_992_ = lean_unbox(v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_unsigned_to_nat(1u);
v___x_994_ = lean_nat_add(v_i_986_, v___x_993_);
lean_dec(v_i_986_);
v_i_986_ = v___x_994_;
goto _start;
}
else
{
uint8_t v___x_996_; 
lean_dec(v_k_987_);
lean_dec(v_i_986_);
lean_dec_ref(v_inst_984_);
v___x_996_ = lean_unbox(v___x_991_);
return v___x_996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___redArg___boxed(lean_object* v_inst_997_, lean_object* v_keys_998_, lean_object* v_i_999_, lean_object* v_k_1000_){
_start:
{
uint8_t v_res_1001_; lean_object* v_r_1002_; 
v_res_1001_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_997_, v_keys_998_, v_i_999_, v_k_1000_);
lean_dec_ref(v_keys_998_);
v_r_1002_ = lean_box(v_res_1001_);
return v_r_1002_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux(lean_object* v_00_u03b1_1003_, lean_object* v_00_u03b2_1004_, lean_object* v_inst_1005_, lean_object* v_keys_1006_, lean_object* v_vals_1007_, lean_object* v_heq_1008_, lean_object* v_i_1009_, lean_object* v_k_1010_){
_start:
{
uint8_t v___x_1011_; 
v___x_1011_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1005_, v_keys_1006_, v_i_1009_, v_k_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___boxed(lean_object* v_00_u03b1_1012_, lean_object* v_00_u03b2_1013_, lean_object* v_inst_1014_, lean_object* v_keys_1015_, lean_object* v_vals_1016_, lean_object* v_heq_1017_, lean_object* v_i_1018_, lean_object* v_k_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = l_Lean_PersistentHashMap_containsAtAux(v_00_u03b1_1012_, v_00_u03b2_1013_, v_inst_1014_, v_keys_1015_, v_vals_1016_, v_heq_1017_, v_i_1018_, v_k_1019_);
lean_dec_ref(v_vals_1016_);
lean_dec_ref(v_keys_1015_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___redArg(lean_object* v_inst_1022_, lean_object* v_x_1023_, size_t v_x_1024_, lean_object* v_x_1025_){
_start:
{
if (lean_obj_tag(v_x_1023_) == 0)
{
lean_object* v_es_1026_; lean_object* v___x_1027_; size_t v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; lean_object* v_j_1031_; lean_object* v___x_1032_; 
v_es_1026_ = lean_ctor_get(v_x_1023_, 0);
lean_inc_ref(v_es_1026_);
lean_dec_ref(v_x_1023_);
v___x_1027_ = lean_box(2);
v___x_1028_ = ((size_t)5ULL);
v___x_1029_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_1030_ = lean_usize_land(v_x_1024_, v___x_1029_);
v_j_1031_ = lean_usize_to_nat(v___x_1030_);
v___x_1032_ = lean_array_get(v___x_1027_, v_es_1026_, v_j_1031_);
lean_dec(v_j_1031_);
lean_dec_ref(v_es_1026_);
switch(lean_obj_tag(v___x_1032_))
{
case 0:
{
lean_object* v_key_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_key_1033_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_key_1033_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = lean_apply_2(v_inst_1022_, v_x_1025_, v_key_1033_);
v___x_1035_ = lean_unbox(v___x_1034_);
return v___x_1035_;
}
case 1:
{
lean_object* v_node_1036_; size_t v___x_1037_; 
v_node_1036_ = lean_ctor_get(v___x_1032_, 0);
lean_inc(v_node_1036_);
lean_dec_ref(v___x_1032_);
v___x_1037_ = lean_usize_shift_right(v_x_1024_, v___x_1028_);
v_x_1023_ = v_node_1036_;
v_x_1024_ = v___x_1037_;
goto _start;
}
default: 
{
uint8_t v___x_1039_; 
lean_dec(v_x_1025_);
lean_dec_ref(v_inst_1022_);
v___x_1039_ = 0;
return v___x_1039_;
}
}
}
else
{
lean_object* v_ks_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_ks_1040_ = lean_ctor_get(v_x_1023_, 0);
lean_inc_ref(v_ks_1040_);
lean_dec_ref(v_x_1023_);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1022_, v_ks_1040_, v___x_1041_, v_x_1025_);
lean_dec_ref(v_ks_1040_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___redArg___boxed(lean_object* v_inst_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
size_t v_x_110__boxed_1047_; uint8_t v_res_1048_; lean_object* v_r_1049_; 
v_x_110__boxed_1047_ = lean_unbox_usize(v_x_1045_);
lean_dec(v_x_1045_);
v_res_1048_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1043_, v_x_1044_, v_x_110__boxed_1047_, v_x_1046_);
v_r_1049_ = lean_box(v_res_1048_);
return v_r_1049_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_inst_1052_, lean_object* v_x_1053_, size_t v_x_1054_, lean_object* v_x_1055_){
_start:
{
uint8_t v___x_1056_; 
v___x_1056_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1052_, v_x_1053_, v_x_1054_, v_x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___boxed(lean_object* v_00_u03b1_1057_, lean_object* v_00_u03b2_1058_, lean_object* v_inst_1059_, lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
size_t v_x_158__boxed_1063_; uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_x_158__boxed_1063_ = lean_unbox_usize(v_x_1061_);
lean_dec(v_x_1061_);
v_res_1064_ = l_Lean_PersistentHashMap_containsAux(v_00_u03b1_1057_, v_00_u03b2_1058_, v_inst_1059_, v_x_1060_, v_x_158__boxed_1063_, v_x_1062_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
lean_object* v___x_1070_; uint64_t v___x_1071_; size_t v___x_1072_; uint8_t v___x_1073_; 
lean_inc(v_x_1069_);
v___x_1070_ = lean_apply_1(v_inst_1067_, v_x_1069_);
v___x_1071_ = lean_unbox_uint64(v___x_1070_);
lean_dec_ref(v___x_1070_);
v___x_1072_ = lean_uint64_to_usize(v___x_1071_);
v___x_1073_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1066_, v_x_1068_, v___x_1072_, v_x_1069_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___redArg___boxed(lean_object* v_inst_1074_, lean_object* v_inst_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
uint8_t v_res_1078_; lean_object* v_r_1079_; 
v_res_1078_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1074_, v_inst_1075_, v_x_1076_, v_x_1077_);
v_r_1079_ = lean_box(v_res_1078_);
return v_r_1079_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains(lean_object* v_00_u03b1_1080_, lean_object* v_00_u03b2_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1082_, v_inst_1083_, v_x_1084_, v_x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___boxed(lean_object* v_00_u03b1_1087_, lean_object* v_00_u03b2_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_x_1091_, lean_object* v_x_1092_){
_start:
{
uint8_t v_res_1093_; lean_object* v_r_1094_; 
v_res_1093_ = l_Lean_PersistentHashMap_contains(v_00_u03b1_1087_, v_00_u03b2_1088_, v_inst_1089_, v_inst_1090_, v_x_1091_, v_x_1092_);
v_r_1094_ = lean_box(v_res_1093_);
return v_r_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg(lean_object* v_a_1095_, lean_object* v_i_1096_, lean_object* v_acc_1097_){
_start:
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1098_ = lean_array_get_size(v_a_1095_);
v___x_1099_ = lean_nat_dec_lt(v_i_1096_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec(v_i_1096_);
return v_acc_1097_;
}
else
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_array_fget(v_a_1095_, v_i_1096_);
switch(lean_obj_tag(v___x_1100_))
{
case 0:
{
if (lean_obj_tag(v_acc_1097_) == 0)
{
lean_object* v_key_1101_; lean_object* v_val_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1113_; 
v_key_1101_ = lean_ctor_get(v___x_1100_, 0);
v_val_1102_ = lean_ctor_get(v___x_1100_, 1);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1100_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1104_ = v___x_1100_;
v_isShared_1105_ = v_isSharedCheck_1113_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_val_1102_);
lean_inc(v_key_1101_);
lean_dec(v___x_1100_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1113_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1106_ = lean_unsigned_to_nat(1u);
v___x_1107_ = lean_nat_add(v_i_1096_, v___x_1106_);
lean_dec(v_i_1096_);
if (v_isShared_1105_ == 0)
{
v___x_1109_ = v___x_1104_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_key_1101_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_val_1102_);
v___x_1109_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
lean_object* v___x_1110_; 
v___x_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
v_i_1096_ = v___x_1107_;
v_acc_1097_ = v___x_1110_;
goto _start;
}
}
}
else
{
lean_object* v___x_1114_; 
lean_dec_ref(v_acc_1097_);
lean_dec_ref(v___x_1100_);
lean_dec(v_i_1096_);
v___x_1114_ = lean_box(0);
return v___x_1114_;
}
}
case 1:
{
lean_object* v___x_1115_; 
lean_dec_ref(v___x_1100_);
lean_dec(v_acc_1097_);
lean_dec(v_i_1096_);
v___x_1115_ = lean_box(0);
return v___x_1115_;
}
default: 
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_add(v_i_1096_, v___x_1116_);
lean_dec(v_i_1096_);
v_i_1096_ = v___x_1117_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg___boxed(lean_object* v_a_1119_, lean_object* v_i_1120_, lean_object* v_acc_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1119_, v_i_1120_, v_acc_1121_);
lean_dec_ref(v_a_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries(lean_object* v_00_u03b1_1123_, lean_object* v_00_u03b2_1124_, lean_object* v_a_1125_, lean_object* v_i_1126_, lean_object* v_acc_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1125_, v_i_1126_, v_acc_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_a_1131_, lean_object* v_i_1132_, lean_object* v_acc_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_PersistentHashMap_isUnaryEntries(v_00_u03b1_1129_, v_00_u03b2_1130_, v_a_1131_, v_i_1132_, v_acc_1133_);
lean_dec_ref(v_a_1131_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object* v_x_1135_){
_start:
{
if (lean_obj_tag(v_x_1135_) == 0)
{
lean_object* v_es_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_es_1136_ = lean_ctor_get(v_x_1135_, 0);
lean_inc_ref(v_es_1136_);
lean_dec_ref(v_x_1135_);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_box(0);
v___x_1139_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_es_1136_, v___x_1137_, v___x_1138_);
lean_dec_ref(v_es_1136_);
return v___x_1139_;
}
else
{
lean_object* v_ks_1140_; lean_object* v_vs_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1156_; 
v_ks_1140_ = lean_ctor_get(v_x_1135_, 0);
v_vs_1141_ = lean_ctor_get(v_x_1135_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_x_1135_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1143_ = v_x_1135_;
v_isShared_1144_ = v_isSharedCheck_1156_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_vs_1141_);
lean_inc(v_ks_1140_);
lean_dec(v_x_1135_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1156_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = lean_array_get_size(v_ks_1140_);
v___x_1147_ = lean_nat_dec_eq(v___x_1145_, v___x_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; 
lean_del_object(v___x_1143_);
lean_dec_ref(v_vs_1141_);
lean_dec_ref(v_ks_1140_);
v___x_1148_ = lean_box(0);
return v___x_1148_;
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = lean_array_fget(v_ks_1140_, v___x_1149_);
lean_dec_ref(v_ks_1140_);
v___x_1151_ = lean_array_fget(v_vs_1141_, v___x_1149_);
lean_dec_ref(v_vs_1141_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 0);
lean_ctor_set(v___x_1143_, 1, v___x_1151_);
lean_ctor_set(v___x_1143_, 0, v___x_1150_);
v___x_1153_ = v___x_1143_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_x_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg(lean_object* v_inst_1161_, lean_object* v_x_1162_, size_t v_x_1163_, lean_object* v_x_1164_){
_start:
{
if (lean_obj_tag(v_x_1162_) == 0)
{
lean_object* v_es_1165_; lean_object* v___x_1166_; size_t v___x_1167_; size_t v___x_1168_; size_t v___x_1169_; lean_object* v_j_1170_; lean_object* v_entry_1171_; 
v_es_1165_ = lean_ctor_get(v_x_1162_, 0);
v___x_1166_ = lean_box(2);
v___x_1167_ = ((size_t)5ULL);
v___x_1168_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___redArg___closed__1);
v___x_1169_ = lean_usize_land(v_x_1163_, v___x_1168_);
v_j_1170_ = lean_usize_to_nat(v___x_1169_);
v_entry_1171_ = lean_array_get(v___x_1166_, v_es_1165_, v_j_1170_);
switch(lean_obj_tag(v_entry_1171_))
{
case 0:
{
lean_object* v_key_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v_key_1172_ = lean_ctor_get(v_entry_1171_, 0);
lean_inc(v_key_1172_);
lean_dec_ref(v_entry_1171_);
v___x_1173_ = lean_apply_2(v_inst_1161_, v_x_1164_, v_key_1172_);
v___x_1174_ = lean_unbox(v___x_1173_);
if (v___x_1174_ == 0)
{
lean_dec(v_j_1170_);
return v_x_1162_;
}
else
{
lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1182_; 
lean_inc_ref(v_es_1165_);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v_x_1162_, 0);
lean_dec(v_unused_1183_);
v___x_1176_ = v_x_1162_;
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
else
{
lean_dec(v_x_1162_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1182_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1178_ = lean_array_set(v_es_1165_, v_j_1170_, v___x_1166_);
lean_dec(v_j_1170_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1178_);
v___x_1180_ = v___x_1176_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
case 1:
{
lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1217_; 
lean_inc_ref(v_es_1165_);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v_x_1162_, 0);
lean_dec(v_unused_1218_);
v___x_1185_ = v_x_1162_;
v_isShared_1186_ = v_isSharedCheck_1217_;
goto v_resetjp_1184_;
}
else
{
lean_dec(v_x_1162_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1217_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_node_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1216_; 
v_node_1187_ = lean_ctor_get(v_entry_1171_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_entry_1171_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1189_ = v_entry_1171_;
v_isShared_1190_ = v_isSharedCheck_1216_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_node_1187_);
lean_dec(v_entry_1171_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1216_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_entries_1191_; size_t v___x_1192_; lean_object* v_newNode_1193_; lean_object* v___x_1194_; 
v_entries_1191_ = lean_array_set(v_es_1165_, v_j_1170_, v___x_1166_);
v___x_1192_ = lean_usize_shift_right(v_x_1163_, v___x_1167_);
v_newNode_1193_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1161_, v_node_1187_, v___x_1192_, v_x_1164_);
lean_inc_ref(v_newNode_1193_);
v___x_1194_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1193_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v___x_1196_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v_newNode_1193_);
v___x_1196_ = v___x_1189_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_newNode_1193_);
v___x_1196_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1197_ = lean_array_set(v_entries_1191_, v_j_1170_, v___x_1196_);
lean_dec(v_j_1170_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1197_);
v___x_1199_ = v___x_1185_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v_val_1202_; lean_object* v_fst_1203_; lean_object* v_snd_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1215_; 
lean_dec_ref(v_newNode_1193_);
lean_del_object(v___x_1189_);
v_val_1202_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_val_1202_);
lean_dec_ref(v___x_1194_);
v_fst_1203_ = lean_ctor_get(v_val_1202_, 0);
v_snd_1204_ = lean_ctor_get(v_val_1202_, 1);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_val_1202_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1206_ = v_val_1202_;
v_isShared_1207_ = v_isSharedCheck_1215_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_snd_1204_);
lean_inc(v_fst_1203_);
lean_dec(v_val_1202_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1215_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_fst_1203_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_snd_1204_);
v___x_1209_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_array_set(v_entries_1191_, v_j_1170_, v___x_1209_);
lean_dec(v_j_1170_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1210_);
v___x_1212_ = v___x_1185_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1170_);
lean_dec(v_x_1164_);
lean_dec_ref(v_inst_1161_);
return v_x_1162_;
}
}
}
else
{
lean_object* v_ks_1219_; lean_object* v_vs_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1234_; 
v_ks_1219_ = lean_ctor_get(v_x_1162_, 0);
v_vs_1220_ = lean_ctor_get(v_x_1162_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_x_1162_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1222_ = v_x_1162_;
v_isShared_1223_ = v_isSharedCheck_1234_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_vs_1220_);
lean_inc(v_ks_1219_);
lean_dec(v_x_1162_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1234_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1224_; 
v___x_1224_ = l_Array_finIdxOf_x3f___redArg(v_inst_1161_, v_ks_1219_, v_x_1164_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v___x_1226_; 
if (v_isShared_1223_ == 0)
{
v___x_1226_ = v___x_1222_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_ks_1219_);
lean_ctor_set(v_reuseFailAlloc_1227_, 1, v_vs_1220_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
else
{
lean_object* v_val_1228_; lean_object* v_keys_x27_1229_; lean_object* v_vals_x27_1230_; lean_object* v___x_1232_; 
v_val_1228_ = lean_ctor_get(v___x_1224_, 0);
lean_inc_n(v_val_1228_, 2);
lean_dec_ref(v___x_1224_);
v_keys_x27_1229_ = l_Array_eraseIdx___redArg(v_ks_1219_, v_val_1228_);
v_vals_x27_1230_ = l_Array_eraseIdx___redArg(v_vs_1220_, v_val_1228_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set(v___x_1222_, 1, v_vals_x27_1230_);
lean_ctor_set(v___x_1222_, 0, v_keys_x27_1229_);
v___x_1232_ = v___x_1222_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_keys_x27_1229_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_vals_x27_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg___boxed(lean_object* v_inst_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_, lean_object* v_x_1238_){
_start:
{
size_t v_x_232__boxed_1239_; lean_object* v_res_1240_; 
v_x_232__boxed_1239_ = lean_unbox_usize(v_x_1237_);
lean_dec(v_x_1237_);
v_res_1240_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1235_, v_x_1236_, v_x_232__boxed_1239_, v_x_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux(lean_object* v_00_u03b1_1241_, lean_object* v_00_u03b2_1242_, lean_object* v_inst_1243_, lean_object* v_x_1244_, size_t v_x_1245_, lean_object* v_x_1246_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1243_, v_x_1244_, v_x_1245_, v_x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___boxed(lean_object* v_00_u03b1_1248_, lean_object* v_00_u03b2_1249_, lean_object* v_inst_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_, lean_object* v_x_1253_){
_start:
{
size_t v_x_375__boxed_1254_; lean_object* v_res_1255_; 
v_x_375__boxed_1254_ = lean_unbox_usize(v_x_1252_);
lean_dec(v_x_1252_);
v_res_1255_ = l_Lean_PersistentHashMap_eraseAux(v_00_u03b1_1248_, v_00_u03b2_1249_, v_inst_1250_, v_x_1251_, v_x_375__boxed_1254_, v_x_1253_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
lean_object* v___x_1260_; uint64_t v___x_1261_; size_t v_h_1262_; lean_object* v___x_1263_; 
lean_inc(v_x_1259_);
v___x_1260_ = lean_apply_1(v_x_1257_, v_x_1259_);
v___x_1261_ = lean_unbox_uint64(v___x_1260_);
lean_dec_ref(v___x_1260_);
v_h_1262_ = lean_uint64_to_usize(v___x_1261_);
v___x_1263_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_x_1256_, v_x_1258_, v_h_1262_, v_x_1259_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase(lean_object* v_00_u03b1_1264_, lean_object* v_00_u03b2_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_PersistentHashMap_erase___redArg(v_x_1266_, v_x_1267_, v_x_1268_, v_x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed(lean_object* v_i_1271_, lean_object* v_inst_1272_, lean_object* v_f_1273_, lean_object* v_keys_1274_, lean_object* v_vals_1275_, lean_object* v_____do__lift_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(v_i_1271_, v_inst_1272_, v_f_1273_, v_keys_1274_, v_vals_1275_, v_____do__lift_1276_);
lean_dec(v_i_1271_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(lean_object* v_inst_1278_, lean_object* v_f_1279_, lean_object* v_keys_1280_, lean_object* v_vals_1281_, lean_object* v_i_1282_, lean_object* v_acc_1283_){
_start:
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = lean_array_get_size(v_keys_1280_);
v___x_1285_ = lean_nat_dec_lt(v_i_1282_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v_toApplicative_1286_; lean_object* v_toPure_1287_; lean_object* v___x_1288_; 
lean_dec(v_i_1282_);
lean_dec_ref(v_vals_1281_);
lean_dec_ref(v_keys_1280_);
lean_dec(v_f_1279_);
v_toApplicative_1286_ = lean_ctor_get(v_inst_1278_, 0);
lean_inc_ref(v_toApplicative_1286_);
lean_dec_ref(v_inst_1278_);
v_toPure_1287_ = lean_ctor_get(v_toApplicative_1286_, 1);
lean_inc(v_toPure_1287_);
lean_dec_ref(v_toApplicative_1286_);
v___x_1288_ = lean_apply_2(v_toPure_1287_, lean_box(0), v_acc_1283_);
return v___x_1288_;
}
else
{
lean_object* v_toBind_1289_; lean_object* v___f_1290_; lean_object* v_k_1291_; lean_object* v_v_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_toBind_1289_ = lean_ctor_get(v_inst_1278_, 1);
lean_inc(v_toBind_1289_);
lean_inc_ref(v_vals_1281_);
lean_inc_ref(v_keys_1280_);
lean_inc(v_f_1279_);
lean_inc(v_i_1282_);
v___f_1290_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1290_, 0, v_i_1282_);
lean_closure_set(v___f_1290_, 1, v_inst_1278_);
lean_closure_set(v___f_1290_, 2, v_f_1279_);
lean_closure_set(v___f_1290_, 3, v_keys_1280_);
lean_closure_set(v___f_1290_, 4, v_vals_1281_);
v_k_1291_ = lean_array_fget(v_keys_1280_, v_i_1282_);
lean_dec_ref(v_keys_1280_);
v_v_1292_ = lean_array_fget(v_vals_1281_, v_i_1282_);
lean_dec(v_i_1282_);
lean_dec_ref(v_vals_1281_);
v___x_1293_ = lean_apply_3(v_f_1279_, v_acc_1283_, v_k_1291_, v_v_1292_);
v___x_1294_ = lean_apply_4(v_toBind_1289_, lean_box(0), lean_box(0), v___x_1293_, v___f_1290_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(lean_object* v_i_1295_, lean_object* v_inst_1296_, lean_object* v_f_1297_, lean_object* v_keys_1298_, lean_object* v_vals_1299_, lean_object* v_____do__lift_1300_){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_nat_add(v_i_1295_, v___x_1301_);
v___x_1303_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1296_, v_f_1297_, v_keys_1298_, v_vals_1299_, v___x_1302_, v_____do__lift_1300_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse(lean_object* v_m_1304_, lean_object* v_inst_1305_, lean_object* v_00_u03c3_1306_, lean_object* v_00_u03b1_1307_, lean_object* v_00_u03b2_1308_, lean_object* v_f_1309_, lean_object* v_keys_1310_, lean_object* v_vals_1311_, lean_object* v_heq_1312_, lean_object* v_i_1313_, lean_object* v_acc_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1305_, v_f_1309_, v_keys_1310_, v_vals_1311_, v_i_1313_, v_acc_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object* v_inst_1316_, lean_object* v_f_1317_, lean_object* v_x_1318_, lean_object* v_x_1319_){
_start:
{
if (lean_obj_tag(v_x_1318_) == 0)
{
lean_object* v_toApplicative_1320_; lean_object* v_toPure_1321_; lean_object* v_es_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_toApplicative_1320_ = lean_ctor_get(v_inst_1316_, 0);
v_toPure_1321_ = lean_ctor_get(v_toApplicative_1320_, 1);
v_es_1322_ = lean_ctor_get(v_x_1318_, 0);
lean_inc_ref(v_es_1322_);
lean_dec_ref(v_x_1318_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = lean_array_get_size(v_es_1322_);
v___x_1325_ = lean_nat_dec_lt(v___x_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
lean_inc(v_toPure_1321_);
lean_dec_ref(v_es_1322_);
lean_dec(v_f_1317_);
lean_dec_ref(v_inst_1316_);
v___x_1326_ = lean_apply_2(v_toPure_1321_, lean_box(0), v_x_1319_);
return v___x_1326_;
}
else
{
lean_object* v___f_1327_; uint8_t v___x_1328_; 
lean_inc(v_toPure_1321_);
lean_inc_ref(v_inst_1316_);
v___f_1327_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1327_, 0, v_f_1317_);
lean_closure_set(v___f_1327_, 1, v_inst_1316_);
lean_closure_set(v___f_1327_, 2, v_toPure_1321_);
v___x_1328_ = lean_nat_dec_le(v___x_1324_, v___x_1324_);
if (v___x_1328_ == 0)
{
if (v___x_1325_ == 0)
{
lean_object* v___x_1329_; 
lean_inc(v_toPure_1321_);
lean_dec_ref(v___f_1327_);
lean_dec_ref(v_es_1322_);
lean_dec_ref(v_inst_1316_);
v___x_1329_ = lean_apply_2(v_toPure_1321_, lean_box(0), v_x_1319_);
return v___x_1329_;
}
else
{
size_t v___x_1330_; size_t v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = ((size_t)0ULL);
v___x_1331_ = lean_usize_of_nat(v___x_1324_);
v___x_1332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1316_, v___f_1327_, v_es_1322_, v___x_1330_, v___x_1331_, v_x_1319_);
return v___x_1332_;
}
}
else
{
size_t v___x_1333_; size_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = ((size_t)0ULL);
v___x_1334_ = lean_usize_of_nat(v___x_1324_);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1316_, v___f_1327_, v_es_1322_, v___x_1333_, v___x_1334_, v_x_1319_);
return v___x_1335_;
}
}
}
else
{
lean_object* v_ks_1336_; lean_object* v_vs_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v_ks_1336_ = lean_ctor_get(v_x_1318_, 0);
lean_inc_ref(v_ks_1336_);
v_vs_1337_ = lean_ctor_get(v_x_1318_, 1);
lean_inc_ref(v_vs_1337_);
lean_dec_ref(v_x_1318_);
v___x_1338_ = lean_unsigned_to_nat(0u);
v___x_1339_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1316_, v_f_1317_, v_ks_1336_, v_vs_1337_, v___x_1338_, v_x_1319_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0(lean_object* v_f_1340_, lean_object* v_inst_1341_, lean_object* v_toPure_1342_, lean_object* v_acc_1343_, lean_object* v_entry_1344_){
_start:
{
switch(lean_obj_tag(v_entry_1344_))
{
case 0:
{
lean_object* v_key_1345_; lean_object* v_val_1346_; lean_object* v___x_1347_; 
lean_dec(v_toPure_1342_);
lean_dec_ref(v_inst_1341_);
v_key_1345_ = lean_ctor_get(v_entry_1344_, 0);
lean_inc(v_key_1345_);
v_val_1346_ = lean_ctor_get(v_entry_1344_, 1);
lean_inc(v_val_1346_);
lean_dec_ref(v_entry_1344_);
v___x_1347_ = lean_apply_3(v_f_1340_, v_acc_1343_, v_key_1345_, v_val_1346_);
return v___x_1347_;
}
case 1:
{
lean_object* v_node_1348_; lean_object* v___x_1349_; 
lean_dec(v_toPure_1342_);
v_node_1348_ = lean_ctor_get(v_entry_1344_, 0);
lean_inc(v_node_1348_);
lean_dec_ref(v_entry_1344_);
v___x_1349_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1341_, v_f_1340_, v_node_1348_, v_acc_1343_);
return v___x_1349_;
}
default: 
{
lean_object* v___x_1350_; 
lean_dec_ref(v_inst_1341_);
lean_dec(v_f_1340_);
v___x_1350_ = lean_apply_2(v_toPure_1342_, lean_box(0), v_acc_1343_);
return v___x_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux(lean_object* v_m_1351_, lean_object* v_inst_1352_, lean_object* v_00_u03c3_1353_, lean_object* v_00_u03b1_1354_, lean_object* v_00_u03b2_1355_, lean_object* v_f_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1352_, v_f_1356_, v_x_1357_, v_x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___redArg(lean_object* v_inst_1360_, lean_object* v_map_1361_, lean_object* v_f_1362_, lean_object* v_init_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1360_, v_f_1362_, v_map_1361_, v_init_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM(lean_object* v_m_1365_, lean_object* v_inst_1366_, lean_object* v_00_u03c3_1367_, lean_object* v_00_u03b1_1368_, lean_object* v_00_u03b2_1369_, lean_object* v_x_1370_, lean_object* v_x_1371_, lean_object* v_map_1372_, lean_object* v_f_1373_, lean_object* v_init_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1366_, v_f_1373_, v_map_1372_, v_init_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___boxed(lean_object* v_m_1376_, lean_object* v_inst_1377_, lean_object* v_00_u03c3_1378_, lean_object* v_00_u03b1_1379_, lean_object* v_00_u03b2_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_, lean_object* v_map_1383_, lean_object* v_f_1384_, lean_object* v_init_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_PersistentHashMap_foldlM(v_m_1376_, v_inst_1377_, v_00_u03c3_1378_, v_00_u03b1_1379_, v_00_u03b2_1380_, v_x_1381_, v_x_1382_, v_map_1383_, v_f_1384_, v_init_1385_);
lean_dec_ref(v_x_1382_);
lean_dec_ref(v_x_1381_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg___lam__0(lean_object* v_f_1387_, lean_object* v_x_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_apply_2(v_f_1387_, v___y_1389_, v___y_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg(lean_object* v_inst_1392_, lean_object* v_map_1393_, lean_object* v_f_1394_){
_start:
{
lean_object* v___f_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___f_1395_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1395_, 0, v_f_1394_);
v___x_1396_ = lean_box(0);
v___x_1397_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1392_, v___f_1395_, v_map_1393_, v___x_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM(lean_object* v_m_1398_, lean_object* v_inst_1399_, lean_object* v_00_u03b1_1400_, lean_object* v_00_u03b2_1401_, lean_object* v_x_1402_, lean_object* v_x_1403_, lean_object* v_map_1404_, lean_object* v_f_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_1399_, v_map_1404_, v_f_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___boxed(lean_object* v_m_1407_, lean_object* v_inst_1408_, lean_object* v_00_u03b1_1409_, lean_object* v_00_u03b2_1410_, lean_object* v_x_1411_, lean_object* v_x_1412_, lean_object* v_map_1413_, lean_object* v_f_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_PersistentHashMap_forM(v_m_1407_, v_inst_1408_, v_00_u03b1_1409_, v_00_u03b2_1410_, v_x_1411_, v_x_1412_, v_map_1413_, v_f_1414_);
lean_dec_ref(v_x_1412_);
lean_dec_ref(v_x_1411_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg___lam__0(lean_object* v_f_1416_, lean_object* v_x1_1417_, lean_object* v_x2_1418_, lean_object* v_x3_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_apply_3(v_f_1416_, v_x1_1417_, v_x2_1418_, v_x3_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object* v_map_1440_, lean_object* v_f_1441_, lean_object* v_init_1442_){
_start:
{
lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___f_1443_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1443_, 0, v_f_1441_);
v___x_1444_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1445_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1444_, v___f_1443_, v_map_1440_, v_init_1442_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl(lean_object* v_00_u03c3_1446_, lean_object* v_00_u03b1_1447_, lean_object* v_00_u03b2_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_, lean_object* v_map_1451_, lean_object* v_f_1452_, lean_object* v_init_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_1451_, v_f_1452_, v_init_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___boxed(lean_object* v_00_u03c3_1455_, lean_object* v_00_u03b1_1456_, lean_object* v_00_u03b2_1457_, lean_object* v_x_1458_, lean_object* v_x_1459_, lean_object* v_map_1460_, lean_object* v_f_1461_, lean_object* v_init_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_PersistentHashMap_foldl(v_00_u03c3_1455_, v_00_u03b1_1456_, v_00_u03b2_1457_, v_x_1458_, v_x_1459_, v_map_1460_, v_f_1461_, v_init_1462_);
lean_dec_ref(v_x_1459_);
lean_dec_ref(v_x_1458_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__0(lean_object* v_x_1464_){
_start:
{
if (lean_obj_tag(v_x_1464_) == 0)
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
v_a_1465_ = lean_ctor_get(v_x_1464_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_x_1464_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v_x_1464_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v_x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_a_1473_ = lean_ctor_get(v_x_1464_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_x_1464_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v_x_1464_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v_x_1464_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__1(lean_object* v_toPure_1481_, lean_object* v_result_1482_){
_start:
{
lean_object* v_a_1483_; lean_object* v___x_1484_; 
v_a_1483_ = lean_ctor_get(v_result_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref(v_result_1482_);
v___x_1484_ = lean_apply_2(v_toPure_1481_, lean_box(0), v_a_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__2(lean_object* v_toFunctor_1485_, lean_object* v_f_1486_, lean_object* v_intoError_1487_, lean_object* v_s_1488_, lean_object* v_a_1489_, lean_object* v_b_1490_){
_start:
{
lean_object* v_map_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1500_; 
v_map_1491_ = lean_ctor_get(v_toFunctor_1485_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_toFunctor_1485_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v_toFunctor_1485_, 1);
lean_dec(v_unused_1501_);
v___x_1493_ = v_toFunctor_1485_;
v_isShared_1494_ = v_isSharedCheck_1500_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_map_1491_);
lean_dec(v_toFunctor_1485_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1500_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v_b_1490_);
lean_ctor_set(v___x_1493_, 0, v_a_1489_);
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1489_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_b_1490_);
v___x_1496_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_apply_2(v_f_1486_, v___x_1496_, v_s_1488_);
v___x_1498_ = lean_apply_4(v_map_1491_, lean_box(0), lean_box(0), v_intoError_1487_, v___x_1497_);
return v___x_1498_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg(lean_object* v_inst_1503_, lean_object* v_map_1504_, lean_object* v_init_1505_, lean_object* v_f_1506_){
_start:
{
lean_object* v_toApplicative_1507_; lean_object* v_toBind_1508_; lean_object* v___f_1509_; lean_object* v___f_1510_; lean_object* v___f_1511_; lean_object* v___f_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v_toFunctor_1519_; lean_object* v_toPure_1520_; lean_object* v_intoError_1521_; lean_object* v___f_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_toApplicative_1507_ = lean_ctor_get(v_inst_1503_, 0);
lean_inc_ref(v_toApplicative_1507_);
v_toBind_1508_ = lean_ctor_get(v_inst_1503_, 1);
lean_inc(v_toBind_1508_);
lean_inc_ref_n(v_inst_1503_, 6);
v___f_1509_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1509_, 0, v_inst_1503_);
v___f_1510_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1510_, 0, v_inst_1503_);
v___f_1511_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1511_, 0, v_inst_1503_);
v___f_1512_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1512_, 0, v_inst_1503_);
v___x_1513_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1513_, 0, lean_box(0));
lean_closure_set(v___x_1513_, 1, lean_box(0));
lean_closure_set(v___x_1513_, 2, v_inst_1503_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___f_1509_);
v___x_1515_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1515_, 0, lean_box(0));
lean_closure_set(v___x_1515_, 1, lean_box(0));
lean_closure_set(v___x_1515_, 2, v_inst_1503_);
v___x_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
lean_ctor_set(v___x_1516_, 2, v___f_1510_);
lean_ctor_set(v___x_1516_, 3, v___f_1511_);
lean_ctor_set(v___x_1516_, 4, v___f_1512_);
v___x_1517_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1517_, 0, lean_box(0));
lean_closure_set(v___x_1517_, 1, lean_box(0));
lean_closure_set(v___x_1517_, 2, v_inst_1503_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1516_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v_toFunctor_1519_ = lean_ctor_get(v_toApplicative_1507_, 0);
lean_inc_ref(v_toFunctor_1519_);
v_toPure_1520_ = lean_ctor_get(v_toApplicative_1507_, 1);
lean_inc(v_toPure_1520_);
lean_dec_ref(v_toApplicative_1507_);
v_intoError_1521_ = ((lean_object*)(l_Lean_PersistentHashMap_forIn___redArg___closed__0));
v___f_1522_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1522_, 0, v_toPure_1520_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__2), 6, 3);
lean_closure_set(v___f_1523_, 0, v_toFunctor_1519_);
lean_closure_set(v___f_1523_, 1, v_f_1506_);
lean_closure_set(v___f_1523_, 2, v_intoError_1521_);
v___x_1524_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1518_, v___f_1523_, v_map_1504_, v_init_1505_);
v___x_1525_ = lean_apply_4(v_toBind_1508_, lean_box(0), lean_box(0), v___x_1524_, v___f_1522_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn(lean_object* v_m_1526_, lean_object* v_00_u03c3_1527_, lean_object* v_00_u03b1_1528_, lean_object* v_00_u03b2_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, lean_object* v_inst_1532_, lean_object* v_map_1533_, lean_object* v_init_1534_, lean_object* v_f_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1532_, v_map_1533_, v_init_1534_, v_f_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___boxed(lean_object* v_m_1537_, lean_object* v_00_u03c3_1538_, lean_object* v_00_u03b1_1539_, lean_object* v_00_u03b2_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_, lean_object* v_inst_1543_, lean_object* v_map_1544_, lean_object* v_init_1545_, lean_object* v_f_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_PersistentHashMap_forIn(v_m_1537_, v_00_u03c3_1538_, v_00_u03b1_1539_, v_00_u03b2_1540_, v_x_1541_, v_x_1542_, v_inst_1543_, v_map_1544_, v_init_1545_, v_f_1546_);
lean_dec_ref(v_x_1542_);
lean_dec_ref(v_x_1541_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_inst_1548_, lean_object* v_00_u03b2_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1548_, v___y_1550_, v___y_1551_, v___y_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1554_){
_start:
{
lean_object* v___f_1555_; 
v___f_1555_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1555_, 0, v_inst_1554_);
return v___f_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad(lean_object* v_m_1556_, lean_object* v_00_u03b1_1557_, lean_object* v_00_u03b2_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_, lean_object* v_inst_1561_){
_start:
{
lean_object* v___f_1562_; 
v___f_1562_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_1562_, 0, v_inst_1561_);
return v___f_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___boxed(lean_object* v_m_1563_, lean_object* v_00_u03b1_1564_, lean_object* v_00_u03b2_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v_inst_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_PersistentHashMap_instForInProdOfMonad(v_m_1563_, v_00_u03b1_1564_, v_00_u03b2_1565_, v_x_1566_, v_x_1567_, v_inst_1568_);
lean_dec_ref(v_x_1567_);
lean_dec_ref(v_x_1566_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__0(lean_object* v_toPure_1570_, lean_object* v_entries_x27_1571_){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v_entries_x27_1571_);
v___x_1573_ = lean_apply_2(v_toPure_1570_, lean_box(0), v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__1(lean_object* v_toPure_1574_, lean_object* v_____do__lift_1575_){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_____do__lift_1575_);
v___x_1577_ = lean_apply_2(v_toPure_1574_, lean_box(0), v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__2(lean_object* v_key_1578_, lean_object* v_toPure_1579_, lean_object* v_____do__lift_1580_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v_key_1578_);
lean_ctor_set(v___x_1581_, 1, v_____do__lift_1580_);
v___x_1582_ = lean_apply_2(v_toPure_1579_, lean_box(0), v___x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__4(lean_object* v_ks_1583_, lean_object* v_toPure_1584_, lean_object* v_____x_1585_){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1586_, 0, v_ks_1583_);
lean_ctor_set(v___x_1586_, 1, v_____x_1585_);
v___x_1587_ = lean_apply_2(v_toPure_1584_, lean_box(0), v___x_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg(lean_object* v_inst_1588_, lean_object* v_f_1589_, lean_object* v_n_1590_){
_start:
{
if (lean_obj_tag(v_n_1590_) == 0)
{
lean_object* v_toApplicative_1591_; lean_object* v_toBind_1592_; lean_object* v_toPure_1593_; lean_object* v_es_1594_; lean_object* v___f_1595_; lean_object* v___f_1596_; lean_object* v___f_1597_; size_t v_sz_1598_; size_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_toApplicative_1591_ = lean_ctor_get(v_inst_1588_, 0);
v_toBind_1592_ = lean_ctor_get(v_inst_1588_, 1);
lean_inc_n(v_toBind_1592_, 2);
v_toPure_1593_ = lean_ctor_get(v_toApplicative_1591_, 1);
v_es_1594_ = lean_ctor_get(v_n_1590_, 0);
lean_inc_ref(v_es_1594_);
lean_dec_ref(v_n_1590_);
lean_inc_n(v_toPure_1593_, 3);
v___f_1595_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1595_, 0, v_toPure_1593_);
v___f_1596_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1596_, 0, v_toPure_1593_);
lean_inc_ref(v_inst_1588_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1597_, 0, v_toPure_1593_);
lean_closure_set(v___f_1597_, 1, v_f_1589_);
lean_closure_set(v___f_1597_, 2, v_toBind_1592_);
lean_closure_set(v___f_1597_, 3, v_inst_1588_);
lean_closure_set(v___f_1597_, 4, v___f_1596_);
v_sz_1598_ = lean_array_size(v_es_1594_);
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1588_, v___f_1597_, v_sz_1598_, v___x_1599_, v_es_1594_);
v___x_1601_ = lean_apply_4(v_toBind_1592_, lean_box(0), lean_box(0), v___x_1600_, v___f_1595_);
return v___x_1601_;
}
else
{
lean_object* v_toApplicative_1602_; lean_object* v_toBind_1603_; lean_object* v_toPure_1604_; lean_object* v_ks_1605_; lean_object* v_vs_1606_; lean_object* v___f_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_toApplicative_1602_ = lean_ctor_get(v_inst_1588_, 0);
v_toBind_1603_ = lean_ctor_get(v_inst_1588_, 1);
lean_inc(v_toBind_1603_);
v_toPure_1604_ = lean_ctor_get(v_toApplicative_1602_, 1);
v_ks_1605_ = lean_ctor_get(v_n_1590_, 0);
lean_inc_ref(v_ks_1605_);
v_vs_1606_ = lean_ctor_get(v_n_1590_, 1);
lean_inc_ref(v_vs_1606_);
lean_dec_ref(v_n_1590_);
lean_inc(v_toPure_1604_);
v___f_1607_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__4), 3, 2);
lean_closure_set(v___f_1607_, 0, v_ks_1605_);
lean_closure_set(v___f_1607_, 1, v_toPure_1604_);
v___x_1608_ = l_Array_mapM_x27___redArg(v_inst_1588_, v_f_1589_, v_vs_1606_);
v___x_1609_ = lean_apply_4(v_toBind_1603_, lean_box(0), lean_box(0), v___x_1608_, v___f_1607_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__3(lean_object* v_toPure_1610_, lean_object* v_f_1611_, lean_object* v_toBind_1612_, lean_object* v_inst_1613_, lean_object* v___f_1614_, lean_object* v_x_1615_){
_start:
{
switch(lean_obj_tag(v_x_1615_))
{
case 0:
{
lean_object* v_key_1616_; lean_object* v_val_1617_; lean_object* v___f_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec(v___f_1614_);
lean_dec_ref(v_inst_1613_);
v_key_1616_ = lean_ctor_get(v_x_1615_, 0);
lean_inc(v_key_1616_);
v_val_1617_ = lean_ctor_get(v_x_1615_, 1);
lean_inc(v_val_1617_);
lean_dec_ref(v_x_1615_);
v___f_1618_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1618_, 0, v_key_1616_);
lean_closure_set(v___f_1618_, 1, v_toPure_1610_);
v___x_1619_ = lean_apply_1(v_f_1611_, v_val_1617_);
v___x_1620_ = lean_apply_4(v_toBind_1612_, lean_box(0), lean_box(0), v___x_1619_, v___f_1618_);
return v___x_1620_;
}
case 1:
{
lean_object* v_node_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
lean_dec(v_toPure_1610_);
v_node_1621_ = lean_ctor_get(v_x_1615_, 0);
lean_inc(v_node_1621_);
lean_dec_ref(v_x_1615_);
v___x_1622_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1613_, v_f_1611_, v_node_1621_);
v___x_1623_ = lean_apply_4(v_toBind_1612_, lean_box(0), lean_box(0), v___x_1622_, v___f_1614_);
return v___x_1623_;
}
default: 
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
lean_dec(v___f_1614_);
lean_dec_ref(v_inst_1613_);
lean_dec(v_toBind_1612_);
lean_dec(v_f_1611_);
v___x_1624_ = lean_box(2);
v___x_1625_ = lean_apply_2(v_toPure_1610_, lean_box(0), v___x_1624_);
return v___x_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux(lean_object* v_00_u03b1_1626_, lean_object* v_00_u03b2_1627_, lean_object* v_00_u03c3_1628_, lean_object* v_m_1629_, lean_object* v_inst_1630_, lean_object* v_f_1631_, lean_object* v_n_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1630_, v_f_1631_, v_n_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg___lam__0(lean_object* v_toPure_1634_, lean_object* v_root_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_apply_2(v_toPure_1634_, lean_box(0), v_root_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object* v_inst_1637_, lean_object* v_pm_1638_, lean_object* v_f_1639_){
_start:
{
lean_object* v_toApplicative_1640_; lean_object* v_toBind_1641_; lean_object* v_toPure_1642_; lean_object* v___x_1643_; lean_object* v___f_1644_; lean_object* v___x_1645_; 
v_toApplicative_1640_ = lean_ctor_get(v_inst_1637_, 0);
v_toBind_1641_ = lean_ctor_get(v_inst_1637_, 1);
lean_inc(v_toBind_1641_);
v_toPure_1642_ = lean_ctor_get(v_toApplicative_1640_, 1);
lean_inc(v_toPure_1642_);
v___x_1643_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1637_, v_f_1639_, v_pm_1638_);
v___f_1644_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1644_, 0, v_toPure_1642_);
v___x_1645_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v___x_1643_, v___f_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM(lean_object* v_00_u03b1_1646_, lean_object* v_00_u03b2_1647_, lean_object* v_00_u03c3_1648_, lean_object* v_m_1649_, lean_object* v_inst_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_pm_1653_, lean_object* v_f_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_1650_, v_pm_1653_, v_f_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___boxed(lean_object* v_00_u03b1_1656_, lean_object* v_00_u03b2_1657_, lean_object* v_00_u03c3_1658_, lean_object* v_m_1659_, lean_object* v_inst_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_pm_1663_, lean_object* v_f_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_PersistentHashMap_mapM(v_00_u03b1_1656_, v_00_u03b2_1657_, v_00_u03c3_1658_, v_m_1659_, v_inst_1660_, v_x_1661_, v_x_1662_, v_pm_1663_, v_f_1664_);
lean_dec_ref(v_x_1662_);
lean_dec_ref(v_x_1661_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg___lam__0(lean_object* v_f_1666_, lean_object* v_x_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = lean_apply_1(v_f_1666_, v_x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg(lean_object* v_pm_1669_, lean_object* v_f_1670_){
_start:
{
lean_object* v___f_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___f_1671_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1671_, 0, v_f_1670_);
v___x_1672_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1673_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_1672_, v_pm_1669_, v___f_1671_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map(lean_object* v_00_u03b1_1674_, lean_object* v_00_u03b2_1675_, lean_object* v_00_u03c3_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_, lean_object* v_pm_1679_, lean_object* v_f_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_PersistentHashMap_map___redArg(v_pm_1679_, v_f_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___boxed(lean_object* v_00_u03b1_1682_, lean_object* v_00_u03b2_1683_, lean_object* v_00_u03c3_1684_, lean_object* v_x_1685_, lean_object* v_x_1686_, lean_object* v_pm_1687_, lean_object* v_f_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_PersistentHashMap_map(v_00_u03b1_1682_, v_00_u03b2_1683_, v_00_u03c3_1684_, v_x_1685_, v_x_1686_, v_pm_1687_, v_f_1688_);
lean_dec_ref(v_x_1686_);
lean_dec_ref(v_x_1685_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg___lam__0(lean_object* v_ps_1690_, lean_object* v_k_1691_, lean_object* v_v_1692_){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_k_1691_);
lean_ctor_set(v___x_1693_, 1, v_v_1692_);
v___x_1694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v_ps_1690_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg(lean_object* v_m_1696_){
_start:
{
lean_object* v___f_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___f_1697_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___redArg___closed__0));
v___x_1698_ = lean_box(0);
v___x_1699_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1696_, v___f_1697_, v___x_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList(lean_object* v_00_u03b1_1700_, lean_object* v_00_u03b2_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_, lean_object* v_m_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_PersistentHashMap_toList___redArg(v_m_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___boxed(lean_object* v_00_u03b1_1706_, lean_object* v_00_u03b2_1707_, lean_object* v_x_1708_, lean_object* v_x_1709_, lean_object* v_m_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_PersistentHashMap_toList(v_00_u03b1_1706_, v_00_u03b2_1707_, v_x_1708_, v_x_1709_, v_m_1710_);
lean_dec_ref(v_x_1709_);
lean_dec_ref(v_x_1708_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg___lam__0(lean_object* v_ps_1712_, lean_object* v_k_1713_, lean_object* v_v_1714_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v_k_1713_);
lean_ctor_set(v___x_1715_, 1, v_v_1714_);
v___x_1716_ = lean_array_push(v_ps_1712_, v___x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg(lean_object* v_m_1720_){
_start:
{
lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___f_1721_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__0));
v___x_1722_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__1));
v___x_1723_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1720_, v___f_1721_, v___x_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray(lean_object* v_00_u03b1_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_x_1726_, lean_object* v_x_1727_, lean_object* v_m_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Lean_PersistentHashMap_toArray___redArg(v_m_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___boxed(lean_object* v_00_u03b1_1730_, lean_object* v_00_u03b2_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_, lean_object* v_m_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lean_PersistentHashMap_toArray(v_00_u03b1_1730_, v_00_u03b2_1731_, v_x_1732_, v_x_1733_, v_m_1734_);
lean_dec_ref(v_x_1733_);
lean_dec_ref(v_x_1732_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg(lean_object* v_x_1736_, lean_object* v_x_1737_, lean_object* v_x_1738_){
_start:
{
if (lean_obj_tag(v_x_1736_) == 0)
{
lean_object* v_es_1739_; lean_object* v_numNodes_1740_; lean_object* v_numNull_1741_; lean_object* v_numCollisions_1742_; lean_object* v_maxDepth_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1765_; 
v_es_1739_ = lean_ctor_get(v_x_1736_, 0);
v_numNodes_1740_ = lean_ctor_get(v_x_1737_, 0);
v_numNull_1741_ = lean_ctor_get(v_x_1737_, 1);
v_numCollisions_1742_ = lean_ctor_get(v_x_1737_, 2);
v_maxDepth_1743_ = lean_ctor_get(v_x_1737_, 3);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_x_1737_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1745_ = v_x_1737_;
v_isShared_1746_ = v_isSharedCheck_1765_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_maxDepth_1743_);
lean_inc(v_numCollisions_1742_);
lean_inc(v_numNull_1741_);
lean_inc(v_numNodes_1740_);
lean_dec(v_x_1737_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1765_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___y_1750_; uint8_t v___x_1764_; 
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = lean_nat_add(v_numNodes_1740_, v___x_1747_);
lean_dec(v_numNodes_1740_);
v___x_1764_ = lean_nat_dec_le(v_maxDepth_1743_, v_x_1738_);
if (v___x_1764_ == 0)
{
v___y_1750_ = v_maxDepth_1743_;
goto v___jp_1749_;
}
else
{
lean_dec(v_maxDepth_1743_);
lean_inc(v_x_1738_);
v___y_1750_ = v_x_1738_;
goto v___jp_1749_;
}
v___jp_1749_:
{
lean_object* v_stats_1752_; 
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 3, v___y_1750_);
lean_ctor_set(v___x_1745_, 0, v___x_1748_);
v_stats_1752_ = v___x_1745_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_numNull_1741_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_numCollisions_1742_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v___y_1750_);
v_stats_1752_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = lean_array_get_size(v_es_1739_);
v___x_1755_ = lean_nat_dec_lt(v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_dec(v_x_1738_);
return v_stats_1752_;
}
else
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_nat_dec_le(v___x_1754_, v___x_1754_);
if (v___x_1756_ == 0)
{
if (v___x_1755_ == 0)
{
lean_dec(v_x_1738_);
return v_stats_1752_;
}
else
{
size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = ((size_t)0ULL);
v___x_1758_ = lean_usize_of_nat(v___x_1754_);
v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1738_, v_es_1739_, v___x_1757_, v___x_1758_, v_stats_1752_);
lean_dec(v_x_1738_);
return v___x_1759_;
}
}
else
{
size_t v___x_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = ((size_t)0ULL);
v___x_1761_ = lean_usize_of_nat(v___x_1754_);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1738_, v_es_1739_, v___x_1760_, v___x_1761_, v_stats_1752_);
lean_dec(v_x_1738_);
return v___x_1762_;
}
}
}
}
}
}
else
{
lean_object* v_ks_1766_; lean_object* v_numNodes_1767_; lean_object* v_numNull_1768_; lean_object* v_numCollisions_1769_; lean_object* v_maxDepth_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1786_; 
v_ks_1766_ = lean_ctor_get(v_x_1736_, 0);
v_numNodes_1767_ = lean_ctor_get(v_x_1737_, 0);
v_numNull_1768_ = lean_ctor_get(v_x_1737_, 1);
v_numCollisions_1769_ = lean_ctor_get(v_x_1737_, 2);
v_maxDepth_1770_ = lean_ctor_get(v_x_1737_, 3);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_x_1737_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1772_ = v_x_1737_;
v_isShared_1773_ = v_isSharedCheck_1786_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_maxDepth_1770_);
lean_inc(v_numCollisions_1769_);
lean_inc(v_numNull_1768_);
lean_inc(v_numNodes_1767_);
lean_dec(v_x_1737_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1786_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1774_ = lean_unsigned_to_nat(1u);
v___x_1775_ = lean_nat_add(v_numNodes_1767_, v___x_1774_);
lean_dec(v_numNodes_1767_);
v___x_1776_ = lean_array_get_size(v_ks_1766_);
v___x_1777_ = lean_nat_add(v_numCollisions_1769_, v___x_1776_);
lean_dec(v_numCollisions_1769_);
v___x_1778_ = lean_nat_sub(v___x_1777_, v___x_1774_);
lean_dec(v___x_1777_);
v___x_1779_ = lean_nat_dec_le(v_maxDepth_1770_, v_x_1738_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1781_; 
lean_dec(v_x_1738_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 2, v___x_1778_);
lean_ctor_set(v___x_1772_, 0, v___x_1775_);
v___x_1781_ = v___x_1772_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_numNull_1768_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v_maxDepth_1770_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
else
{
lean_object* v___x_1784_; 
lean_dec(v_maxDepth_1770_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 3, v_x_1738_);
lean_ctor_set(v___x_1772_, 2, v___x_1778_);
lean_ctor_set(v___x_1772_, 0, v___x_1775_);
v___x_1784_ = v___x_1772_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_numNull_1768_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_x_1738_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(lean_object* v_x_1787_, lean_object* v_as_1788_, size_t v_i_1789_, size_t v_stop_1790_, lean_object* v_b_1791_){
_start:
{
lean_object* v___y_1793_; uint8_t v___x_1797_; 
v___x_1797_ = lean_usize_dec_eq(v_i_1789_, v_stop_1790_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_array_uget_borrowed(v_as_1788_, v_i_1789_);
switch(lean_obj_tag(v___x_1799_))
{
case 0:
{
v___y_1793_ = v_b_1791_;
goto v___jp_1792_;
}
case 1:
{
lean_object* v_node_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v_node_1800_ = lean_ctor_get(v___x_1799_, 0);
v___x_1801_ = lean_nat_add(v_x_1787_, v___x_1798_);
v___x_1802_ = l_Lean_PersistentHashMap_collectStats___redArg(v_node_1800_, v_b_1791_, v___x_1801_);
v___y_1793_ = v___x_1802_;
goto v___jp_1792_;
}
default: 
{
lean_object* v_numNodes_1803_; lean_object* v_numNull_1804_; lean_object* v_numCollisions_1805_; lean_object* v_maxDepth_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1814_; 
v_numNodes_1803_ = lean_ctor_get(v_b_1791_, 0);
v_numNull_1804_ = lean_ctor_get(v_b_1791_, 1);
v_numCollisions_1805_ = lean_ctor_get(v_b_1791_, 2);
v_maxDepth_1806_ = lean_ctor_get(v_b_1791_, 3);
v_isSharedCheck_1814_ = !lean_is_exclusive(v_b_1791_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1808_ = v_b_1791_;
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_maxDepth_1806_);
lean_inc(v_numCollisions_1805_);
lean_inc(v_numNull_1804_);
lean_inc(v_numNodes_1803_);
lean_dec(v_b_1791_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1814_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_nat_add(v_numNull_1804_, v___x_1798_);
lean_dec(v_numNull_1804_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 1, v___x_1810_);
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_numNodes_1803_);
lean_ctor_set(v_reuseFailAlloc_1813_, 1, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1813_, 2, v_numCollisions_1805_);
lean_ctor_set(v_reuseFailAlloc_1813_, 3, v_maxDepth_1806_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
v___y_1793_ = v___x_1812_;
goto v___jp_1792_;
}
}
}
}
}
else
{
return v_b_1791_;
}
v___jp_1792_:
{
size_t v___x_1794_; size_t v___x_1795_; 
v___x_1794_ = ((size_t)1ULL);
v___x_1795_ = lean_usize_add(v_i_1789_, v___x_1794_);
v_i_1789_ = v___x_1795_;
v_b_1791_ = v___y_1793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg___boxed(lean_object* v_x_1815_, lean_object* v_as_1816_, lean_object* v_i_1817_, lean_object* v_stop_1818_, lean_object* v_b_1819_){
_start:
{
size_t v_i_boxed_1820_; size_t v_stop_boxed_1821_; lean_object* v_res_1822_; 
v_i_boxed_1820_ = lean_unbox_usize(v_i_1817_);
lean_dec(v_i_1817_);
v_stop_boxed_1821_ = lean_unbox_usize(v_stop_1818_);
lean_dec(v_stop_1818_);
v_res_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1815_, v_as_1816_, v_i_boxed_1820_, v_stop_boxed_1821_, v_b_1819_);
lean_dec_ref(v_as_1816_);
lean_dec(v_x_1815_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg___boxed(lean_object* v_x_1823_, lean_object* v_x_1824_, lean_object* v_x_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_1823_, v_x_1824_, v_x_1825_);
lean_dec_ref(v_x_1823_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats(lean_object* v_00_u03b1_1827_, lean_object* v_00_u03b2_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_, lean_object* v_x_1831_){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_1829_, v_x_1830_, v_x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___boxed(lean_object* v_00_u03b1_1833_, lean_object* v_00_u03b2_1834_, lean_object* v_x_1835_, lean_object* v_x_1836_, lean_object* v_x_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_PersistentHashMap_collectStats(v_00_u03b1_1833_, v_00_u03b2_1834_, v_x_1835_, v_x_1836_, v_x_1837_);
lean_dec_ref(v_x_1835_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(lean_object* v_00_u03b1_1839_, lean_object* v_00_u03b2_1840_, lean_object* v_x_1841_, lean_object* v_as_1842_, size_t v_i_1843_, size_t v_stop_1844_, lean_object* v_b_1845_){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1841_, v_as_1842_, v_i_1843_, v_stop_1844_, v_b_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___boxed(lean_object* v_00_u03b1_1847_, lean_object* v_00_u03b2_1848_, lean_object* v_x_1849_, lean_object* v_as_1850_, lean_object* v_i_1851_, lean_object* v_stop_1852_, lean_object* v_b_1853_){
_start:
{
size_t v_i_boxed_1854_; size_t v_stop_boxed_1855_; lean_object* v_res_1856_; 
v_i_boxed_1854_ = lean_unbox_usize(v_i_1851_);
lean_dec(v_i_1851_);
v_stop_boxed_1855_ = lean_unbox_usize(v_stop_1852_);
lean_dec(v_stop_1852_);
v_res_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(v_00_u03b1_1847_, v_00_u03b2_1848_, v_x_1849_, v_as_1850_, v_i_boxed_1854_, v_stop_boxed_1855_, v_b_1853_);
lean_dec_ref(v_as_1850_);
lean_dec(v_x_1849_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg(lean_object* v_m_1859_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = ((lean_object*)(l_Lean_PersistentHashMap_stats___redArg___closed__0));
v___x_1861_ = lean_unsigned_to_nat(1u);
v___x_1862_ = l_Lean_PersistentHashMap_collectStats___redArg(v_m_1859_, v___x_1860_, v___x_1861_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg___boxed(lean_object* v_m_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_PersistentHashMap_stats___redArg(v_m_1863_);
lean_dec_ref(v_m_1863_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats(lean_object* v_00_u03b1_1865_, lean_object* v_00_u03b2_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v_m_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_PersistentHashMap_stats___redArg(v_m_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_, lean_object* v_m_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_PersistentHashMap_stats(v_00_u03b1_1871_, v_00_u03b2_1872_, v_x_1873_, v_x_1874_, v_m_1875_);
lean_dec_ref(v_m_1875_);
lean_dec_ref(v_x_1874_);
lean_dec_ref(v_x_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Stats_toString(lean_object* v_s_1882_){
_start:
{
lean_object* v_numNodes_1883_; lean_object* v_numNull_1884_; lean_object* v_numCollisions_1885_; lean_object* v_maxDepth_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v_numNodes_1883_ = lean_ctor_get(v_s_1882_, 0);
lean_inc(v_numNodes_1883_);
v_numNull_1884_ = lean_ctor_get(v_s_1882_, 1);
lean_inc(v_numNull_1884_);
v_numCollisions_1885_ = lean_ctor_get(v_s_1882_, 2);
lean_inc(v_numCollisions_1885_);
v_maxDepth_1886_ = lean_ctor_get(v_s_1882_, 3);
lean_inc(v_maxDepth_1886_);
lean_dec_ref(v_s_1882_);
v___x_1887_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__0));
v___x_1888_ = l_Nat_reprFast(v_numNodes_1883_);
v___x_1889_ = lean_string_append(v___x_1887_, v___x_1888_);
lean_dec_ref(v___x_1888_);
v___x_1890_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__1));
v___x_1891_ = lean_string_append(v___x_1889_, v___x_1890_);
v___x_1892_ = l_Nat_reprFast(v_numNull_1884_);
v___x_1893_ = lean_string_append(v___x_1891_, v___x_1892_);
lean_dec_ref(v___x_1892_);
v___x_1894_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__2));
v___x_1895_ = lean_string_append(v___x_1893_, v___x_1894_);
v___x_1896_ = l_Nat_reprFast(v_numCollisions_1885_);
v___x_1897_ = lean_string_append(v___x_1895_, v___x_1896_);
lean_dec_ref(v___x_1896_);
v___x_1898_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__3));
v___x_1899_ = lean_string_append(v___x_1897_, v___x_1898_);
v___x_1900_ = l_Nat_reprFast(v_maxDepth_1886_);
v___x_1901_ = lean_string_append(v___x_1899_, v___x_1900_);
lean_dec_ref(v___x_1900_);
v___x_1902_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__4));
v___x_1903_ = lean_string_append(v___x_1901_, v___x_1902_);
return v___x_1903_;
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
