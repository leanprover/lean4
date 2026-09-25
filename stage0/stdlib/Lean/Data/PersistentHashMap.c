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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry___redArg___boxed(lean_object*);
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
static const lean_array_object l_Lean_PersistentHashMap_instInhabitedNode___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_instInhabitedNode___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_instInhabitedNode___redArg___closed__0_value;
static const lean_ctor_object l_Lean_PersistentHashMap_instInhabitedNode___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PersistentHashMap_instInhabitedNode___redArg___closed__0_value)}};
static const lean_object* l_Lean_PersistentHashMap_instInhabitedNode___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_instInhabitedNode___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_instInhabitedNode___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_instInhabitedNode___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_PersistentHashMap_shift;
LEAN_EXPORT size_t l_Lean_PersistentHashMap_branching;
LEAN_EXPORT size_t l_Lean_PersistentHashMap_maxDepth;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_maxCollisions;
static lean_once_cell_t l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_mkEmptyEntries___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry___redArg(){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(2);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry___redArg___boxed(lean_object* v___dummy_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_PersistentHashMap_instInhabitedEntry___redArg();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object* v_00_u03b1_79_, lean_object* v_00_u03b2_80_, lean_object* v_00_u03c3_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_box(2);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___redArg(lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_unsigned_to_nat(0u);
return v___x_84_;
}
else
{
lean_object* v___x_85_; 
v___x_85_ = lean_unsigned_to_nat(1u);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___redArg___boxed(lean_object* v_x_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_PersistentHashMap_Node_ctorIdx___redArg(v_x_86_);
lean_dec_ref(v_x_86_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx(lean_object* v_00_u03b1_88_, lean_object* v_00_u03b2_89_, lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_PersistentHashMap_Node_ctorIdx___redArg(v_x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___boxed(lean_object* v_00_u03b1_92_, lean_object* v_00_u03b2_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_PersistentHashMap_Node_ctorIdx(v_00_u03b1_92_, v_00_u03b2_93_, v_x_94_);
lean_dec_ref(v_x_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim___redArg(lean_object* v_t_96_, lean_object* v_k_97_){
_start:
{
if (lean_obj_tag(v_t_96_) == 0)
{
lean_object* v_es_98_; lean_object* v___x_99_; 
v_es_98_ = lean_ctor_get(v_t_96_, 0);
lean_inc_ref(v_es_98_);
lean_dec_ref_known(v_t_96_, 1);
v___x_99_ = lean_apply_1(v_k_97_, v_es_98_);
return v___x_99_;
}
else
{
lean_object* v_ks_100_; lean_object* v_vs_101_; lean_object* v___x_102_; 
v_ks_100_ = lean_ctor_get(v_t_96_, 0);
lean_inc_ref(v_ks_100_);
v_vs_101_ = lean_ctor_get(v_t_96_, 1);
lean_inc_ref(v_vs_101_);
lean_dec_ref_known(v_t_96_, 2);
v___x_102_ = lean_apply_3(v_k_97_, v_ks_100_, v_vs_101_, lean_box(0));
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim(lean_object* v_00_u03b1_103_, lean_object* v_00_u03b2_104_, lean_object* v_motive__1_105_, lean_object* v_ctorIdx_106_, lean_object* v_t_107_, lean_object* v_h_108_, lean_object* v_k_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_107_, v_k_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim___boxed(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_motive__1_113_, lean_object* v_ctorIdx_114_, lean_object* v_t_115_, lean_object* v_h_116_, lean_object* v_k_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_PersistentHashMap_Node_ctorElim(v_00_u03b1_111_, v_00_u03b2_112_, v_motive__1_113_, v_ctorIdx_114_, v_t_115_, v_h_116_, v_k_117_);
lean_dec(v_ctorIdx_114_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_entries_elim___redArg(lean_object* v_t_119_, lean_object* v_entries_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_119_, v_entries_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_entries_elim(lean_object* v_00_u03b1_122_, lean_object* v_00_u03b2_123_, lean_object* v_motive__1_124_, lean_object* v_t_125_, lean_object* v_h_126_, lean_object* v_entries_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_125_, v_entries_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_collision_elim___redArg(lean_object* v_t_129_, lean_object* v_collision_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_129_, v_collision_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_collision_elim(lean_object* v_00_u03b1_132_, lean_object* v_00_u03b2_133_, lean_object* v_motive__1_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_collision_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_135_, v_collision_137_);
return v___x_138_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
lean_object* v_es_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_es_140_ = lean_ctor_get(v_x_139_, 0);
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_array_get_size(v_es_140_);
v___x_143_ = lean_nat_dec_lt(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
uint8_t v___x_144_; 
v___x_144_ = 1;
return v___x_144_;
}
else
{
if (v___x_143_ == 0)
{
return v___x_143_;
}
else
{
size_t v___x_145_; size_t v___x_146_; uint8_t v___x_147_; 
v___x_145_ = ((size_t)0ULL);
v___x_146_ = lean_usize_of_nat(v___x_142_);
v___x_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_es_140_, v___x_145_, v___x_146_);
if (v___x_147_ == 0)
{
return v___x_143_;
}
else
{
uint8_t v___x_148_; 
v___x_148_ = 0;
return v___x_148_;
}
}
}
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(lean_object* v_as_150_, size_t v_i_151_, size_t v_stop_152_){
_start:
{
uint8_t v___x_157_; 
v___x_157_ = lean_usize_dec_eq(v_i_151_, v_stop_152_);
if (v___x_157_ == 0)
{
uint8_t v___x_158_; lean_object* v___x_159_; 
v___x_158_ = 1;
v___x_159_ = lean_array_uget_borrowed(v_as_150_, v_i_151_);
switch(lean_obj_tag(v___x_159_))
{
case 0:
{
return v___x_158_;
}
case 1:
{
lean_object* v_node_160_; uint8_t v___x_161_; 
v_node_160_ = lean_ctor_get(v___x_159_, 0);
v___x_161_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_node_160_);
if (v___x_161_ == 0)
{
return v___x_158_;
}
else
{
goto v___jp_153_;
}
}
default: 
{
goto v___jp_153_;
}
}
}
else
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
v___jp_153_:
{
size_t v___x_154_; size_t v___x_155_; 
v___x_154_ = ((size_t)1ULL);
v___x_155_ = lean_usize_add(v_i_151_, v___x_154_);
v_i_151_ = v___x_155_;
goto _start;
}
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_isEmpty___redArg___boxed(lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_170_);
lean_dec_ref(v_x_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_Node_isEmpty(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_x_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_isEmpty___boxed(lean_object* v_00_u03b1_177_, lean_object* v_00_u03b2_178_, lean_object* v_x_179_){
_start:
{
uint8_t v_res_180_; lean_object* v_r_181_; 
v_res_180_ = l_Lean_PersistentHashMap_Node_isEmpty(v_00_u03b1_177_, v_00_u03b2_178_, v_x_179_);
lean_dec_ref(v_x_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(lean_object* v_00_u03b1_182_, lean_object* v_00_u03b2_183_, lean_object* v_as_184_, size_t v_i_185_, size_t v_stop_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_as_184_, v_i_185_, v_stop_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___boxed(lean_object* v_00_u03b1_188_, lean_object* v_00_u03b2_189_, lean_object* v_as_190_, lean_object* v_i_191_, lean_object* v_stop_192_){
_start:
{
size_t v_i_boxed_193_; size_t v_stop_boxed_194_; uint8_t v_res_195_; lean_object* v_r_196_; 
v_i_boxed_193_ = lean_unbox_usize(v_i_191_);
lean_dec(v_i_191_);
v_stop_boxed_194_ = lean_unbox_usize(v_stop_192_);
lean_dec(v_stop_192_);
v_res_195_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(v_00_u03b1_188_, v_00_u03b2_189_, v_as_190_, v_i_boxed_193_, v_stop_boxed_194_);
lean_dec_ref(v_as_190_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode___redArg(){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = ((lean_object*)(l_Lean_PersistentHashMap_instInhabitedNode___redArg___closed__1));
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode___redArg___boxed(lean_object* v___dummy_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_PersistentHashMap_instInhabitedNode___redArg();
return v_res_204_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_instInhabitedNode___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PersistentHashMap_instInhabitedNode___redArg();
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode(lean_object* v_00_u03b1_206_, lean_object* v_00_u03b2_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_obj_once(&l_Lean_PersistentHashMap_instInhabitedNode___closed__0, &l_Lean_PersistentHashMap_instInhabitedNode___closed__0_once, _init_l_Lean_PersistentHashMap_instInhabitedNode___closed__0);
return v___x_208_;
}
}
static size_t _init_l_Lean_PersistentHashMap_shift(void){
_start:
{
size_t v___x_209_; 
v___x_209_ = ((size_t)5ULL);
return v___x_209_;
}
}
static size_t _init_l_Lean_PersistentHashMap_branching(void){
_start:
{
size_t v___x_210_; 
v___x_210_ = ((size_t)32ULL);
return v___x_210_;
}
}
static size_t _init_l_Lean_PersistentHashMap_maxDepth(void){
_start:
{
size_t v___x_211_; 
v___x_211_ = ((size_t)7ULL);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_maxCollisions(void){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = lean_unsigned_to_nat(4u);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_box(2);
v___x_214_ = lean_unsigned_to_nat(32u);
v___x_215_ = lean_mk_array(v___x_214_, v___x_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg(){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___boxed(lean_object* v___dummy_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v_res_219_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0(void){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object* v_00_u03b1_221_, lean_object* v_00_u03b2_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0);
return v___x_223_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___redArg(){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___redArg___closed__0, &l_Lean_PersistentHashMap_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___redArg___closed__0);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___redArg___boxed(lean_object* v___dummy_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_PersistentHashMap_empty___redArg();
return v_res_229_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___closed__0(void){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty(lean_object* v_00_u03b1_231_, lean_object* v_00_u03b2_232_, lean_object* v_inst_233_, lean_object* v_inst_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___closed__0, &l_Lean_PersistentHashMap_empty___closed__0_once, _init_l_Lean_PersistentHashMap_empty___closed__0);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___boxed(lean_object* v_00_u03b1_236_, lean_object* v_00_u03b2_237_, lean_object* v_inst_238_, lean_object* v_inst_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_PersistentHashMap_empty(v_00_u03b1_236_, v_00_u03b2_237_, v_inst_238_, v_inst_239_);
lean_dec_ref(v_inst_239_);
lean_dec_ref(v_inst_238_);
return v_res_240_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___redArg(lean_object* v_x_241_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___redArg___boxed(lean_object* v_x_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l_Lean_PersistentHashMap_isEmpty___redArg(v_x_243_);
lean_dec_ref(v_x_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
uint8_t v___x_251_; 
v___x_251_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___boxed(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v_x_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Lean_PersistentHashMap_isEmpty(v_00_u03b1_252_, v_00_u03b2_253_, v_x_254_, v_x_255_, v_x_256_);
lean_dec_ref(v_x_256_);
lean_dec_ref(v_x_255_);
lean_dec_ref(v_x_254_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___redArg___closed__0, &l_Lean_PersistentHashMap_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___redArg___closed__0);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___redArg___boxed(lean_object* v___dummy_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v_res_262_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object* v_00_u03b1_264_, lean_object* v_00_u03b2_265_, lean_object* v_inst_266_, lean_object* v_inst_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = lean_obj_once(&l_Lean_PersistentHashMap_instInhabited___closed__0, &l_Lean_PersistentHashMap_instInhabited___closed__0_once, _init_l_Lean_PersistentHashMap_instInhabited___closed__0);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___boxed(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_inst_271_, lean_object* v_inst_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_PersistentHashMap_instInhabited(v_00_u03b1_269_, v_00_u03b2_270_, v_inst_271_, v_inst_272_);
lean_dec_ref(v_inst_272_);
lean_dec_ref(v_inst_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg(){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___redArg___closed__0, &l_Lean_PersistentHashMap_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___redArg___closed__0);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg___boxed(lean_object* v___dummy_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v_res_277_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_mkEmptyEntries___closed__0(void){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object* v_00_u03b1_279_, lean_object* v_00_u03b2_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntries___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntries___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntries___closed__0);
return v___x_281_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_mul2Shift(size_t v_i_282_, size_t v_shift_283_){
_start:
{
size_t v___x_284_; 
v___x_284_ = lean_usize_shift_left(v_i_282_, v_shift_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mul2Shift___boxed(lean_object* v_i_285_, lean_object* v_shift_286_){
_start:
{
size_t v_i_boxed_287_; size_t v_shift_boxed_288_; size_t v_res_289_; lean_object* v_r_290_; 
v_i_boxed_287_ = lean_unbox_usize(v_i_285_);
lean_dec(v_i_285_);
v_shift_boxed_288_ = lean_unbox_usize(v_shift_286_);
lean_dec(v_shift_286_);
v_res_289_ = l_Lean_PersistentHashMap_mul2Shift(v_i_boxed_287_, v_shift_boxed_288_);
v_r_290_ = lean_box_usize(v_res_289_);
return v_r_290_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_div2Shift(size_t v_i_291_, size_t v_shift_292_){
_start:
{
size_t v___x_293_; 
v___x_293_ = lean_usize_shift_right(v_i_291_, v_shift_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_div2Shift___boxed(lean_object* v_i_294_, lean_object* v_shift_295_){
_start:
{
size_t v_i_boxed_296_; size_t v_shift_boxed_297_; size_t v_res_298_; lean_object* v_r_299_; 
v_i_boxed_296_ = lean_unbox_usize(v_i_294_);
lean_dec(v_i_294_);
v_shift_boxed_297_ = lean_unbox_usize(v_shift_295_);
lean_dec(v_shift_295_);
v_res_298_ = l_Lean_PersistentHashMap_div2Shift(v_i_boxed_296_, v_shift_boxed_297_);
v_r_299_ = lean_box_usize(v_res_298_);
return v_r_299_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_mod2Shift(size_t v_i_300_, size_t v_shift_301_){
_start:
{
size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; 
v___x_302_ = ((size_t)1ULL);
v___x_303_ = lean_usize_shift_left(v___x_302_, v_shift_301_);
v___x_304_ = lean_usize_sub(v___x_303_, v___x_302_);
v___x_305_ = lean_usize_land(v_i_300_, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mod2Shift___boxed(lean_object* v_i_306_, lean_object* v_shift_307_){
_start:
{
size_t v_i_boxed_308_; size_t v_shift_boxed_309_; size_t v_res_310_; lean_object* v_r_311_; 
v_i_boxed_308_ = lean_unbox_usize(v_i_306_);
lean_dec(v_i_306_);
v_shift_boxed_309_ = lean_unbox_usize(v_shift_307_);
lean_dec(v_shift_307_);
v_res_310_ = l_Lean_PersistentHashMap_mod2Shift(v_i_boxed_308_, v_shift_boxed_309_);
v_r_311_ = lean_box_usize(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(lean_object* v_inst_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
lean_object* v_ks_317_; lean_object* v_vs_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_343_; 
v_ks_317_ = lean_ctor_get(v_x_313_, 0);
v_vs_318_ = lean_ctor_get(v_x_313_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_343_ == 0)
{
v___x_320_ = v_x_313_;
v_isShared_321_ = v_isSharedCheck_343_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_vs_318_);
lean_inc(v_ks_317_);
lean_dec(v_x_313_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_343_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_array_get_size(v_ks_317_);
v___x_323_ = lean_nat_dec_lt(v_x_314_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_327_; 
lean_dec(v_x_314_);
lean_dec_ref(v_inst_312_);
v___x_324_ = lean_array_push(v_ks_317_, v_x_315_);
v___x_325_ = lean_array_push(v_vs_318_, v_x_316_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_325_);
lean_ctor_set(v___x_320_, 0, v___x_324_);
v___x_327_ = v___x_320_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_324_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_325_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
else
{
lean_object* v_k_x27_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v_k_x27_329_ = lean_array_fget_borrowed(v_ks_317_, v_x_314_);
lean_inc_ref(v_inst_312_);
lean_inc(v_k_x27_329_);
lean_inc(v_x_315_);
v___x_330_ = lean_apply_2(v_inst_312_, v_x_315_, v_k_x27_329_);
v___x_331_ = lean_unbox(v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_333_; 
if (v_isShared_321_ == 0)
{
v___x_333_ = v___x_320_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_ks_317_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_vs_318_);
v___x_333_ = v_reuseFailAlloc_337_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_add(v_x_314_, v___x_334_);
lean_dec(v_x_314_);
v_x_313_ = v___x_333_;
v_x_314_ = v___x_335_;
goto _start;
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
lean_dec_ref(v_inst_312_);
v___x_338_ = lean_array_fset(v_ks_317_, v_x_314_, v_x_315_);
v___x_339_ = lean_array_fset(v_vs_318_, v_x_314_, v_x_316_);
lean_dec(v_x_314_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_339_);
lean_ctor_set(v___x_320_, 0, v___x_338_);
v___x_341_ = v___x_320_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_339_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux(lean_object* v_00_u03b1_344_, lean_object* v_00_u03b2_345_, lean_object* v_inst_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(v_inst_346_, v_x_347_, v_x_348_, v_x_349_, v_x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(lean_object* v_inst_352_, lean_object* v_n_353_, lean_object* v_k_354_, lean_object* v_v_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(v_inst_352_, v_n_353_, v___x_356_, v_k_354_, v_v_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode(lean_object* v_00_u03b1_358_, lean_object* v_00_u03b2_359_, lean_object* v_inst_360_, lean_object* v_n_361_, lean_object* v_k_362_, lean_object* v_v_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(v_inst_360_, v_n_361_, v_k_362_, v_v_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object* v_x_365_){
_start:
{
lean_object* v_ks_366_; lean_object* v___x_367_; 
v_ks_366_ = lean_ctor_get(v_x_365_, 0);
v___x_367_ = lean_array_get_size(v_ks_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg___boxed(lean_object* v_x_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_368_);
lean_dec_ref(v_x_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_x_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___boxed(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_x_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_PersistentHashMap_getCollisionNodeSize(v_00_u03b1_374_, v_00_u03b2_375_, v_x_376_);
lean_dec_ref(v_x_376_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object* v_k_u2081_378_, lean_object* v_v_u2081_379_, lean_object* v_k_u2082_380_, lean_object* v_v_u2082_381_){
_start:
{
lean_object* v___x_382_; lean_object* v_ks_383_; lean_object* v___x_384_; lean_object* v_ks_385_; lean_object* v___x_386_; lean_object* v_vs_387_; lean_object* v___x_388_; 
v___x_382_ = lean_unsigned_to_nat(4u);
v_ks_383_ = lean_mk_empty_array_with_capacity(v___x_382_);
lean_inc_ref(v_ks_383_);
v___x_384_ = lean_array_push(v_ks_383_, v_k_u2081_378_);
v_ks_385_ = lean_array_push(v___x_384_, v_k_u2082_380_);
v___x_386_ = lean_array_push(v_ks_383_, v_v_u2081_379_);
v_vs_387_ = lean_array_push(v___x_386_, v_v_u2082_381_);
v___x_388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_388_, 0, v_ks_385_);
lean_ctor_set(v___x_388_, 1, v_vs_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode(lean_object* v_00_u03b1_389_, lean_object* v_00_u03b2_390_, lean_object* v_k_u2081_391_, lean_object* v_v_u2081_392_, lean_object* v_k_u2082_393_, lean_object* v_v_u2082_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_k_u2081_391_, v_v_u2081_392_, v_k_u2082_393_, v_v_u2082_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg(lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_x_398_, size_t v_x_399_, size_t v_x_400_, lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v_es_403_; size_t v___x_404_; size_t v___x_405_; lean_object* v_j_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_es_403_ = lean_ctor_get(v_x_398_, 0);
v___x_404_ = ((size_t)31ULL);
v___x_405_ = lean_usize_land(v_x_399_, v___x_404_);
v_j_406_ = lean_usize_to_nat(v___x_405_);
v___x_407_ = lean_array_get_size(v_es_403_);
v___x_408_ = lean_nat_dec_lt(v_j_406_, v___x_407_);
if (v___x_408_ == 0)
{
lean_dec(v_j_406_);
lean_dec(v_x_402_);
lean_dec(v_x_401_);
lean_dec_ref(v_inst_397_);
lean_dec_ref(v_inst_396_);
return v_x_398_;
}
else
{
lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_448_; 
lean_inc_ref(v_es_403_);
v_isSharedCheck_448_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v_x_398_, 0);
lean_dec(v_unused_449_);
v___x_410_ = v_x_398_;
v_isShared_411_ = v_isSharedCheck_448_;
goto v_resetjp_409_;
}
else
{
lean_dec(v_x_398_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_448_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_v_412_; lean_object* v___x_413_; lean_object* v_xs_x27_414_; lean_object* v___y_416_; 
v_v_412_ = lean_array_fget(v_es_403_, v_j_406_);
v___x_413_ = lean_box(0);
v_xs_x27_414_ = lean_array_fset(v_es_403_, v_j_406_, v___x_413_);
switch(lean_obj_tag(v_v_412_))
{
case 0:
{
lean_object* v_key_421_; lean_object* v_val_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_433_; 
lean_dec_ref(v_inst_397_);
v_key_421_ = lean_ctor_get(v_v_412_, 0);
v_val_422_ = lean_ctor_get(v_v_412_, 1);
v_isSharedCheck_433_ = !lean_is_exclusive(v_v_412_);
if (v_isSharedCheck_433_ == 0)
{
v___x_424_ = v_v_412_;
v_isShared_425_ = v_isSharedCheck_433_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_val_422_);
lean_inc(v_key_421_);
lean_dec(v_v_412_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_433_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; uint8_t v___x_427_; 
lean_inc(v_key_421_);
lean_inc(v_x_401_);
v___x_426_ = lean_apply_2(v_inst_396_, v_x_401_, v_key_421_);
v___x_427_ = lean_unbox(v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_del_object(v___x_424_);
v___x_428_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_421_, v_val_422_, v_x_401_, v_x_402_);
v___x_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
v___y_416_ = v___x_429_;
goto v___jp_415_;
}
else
{
lean_object* v___x_431_; 
lean_dec(v_val_422_);
lean_dec(v_key_421_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v_x_402_);
lean_ctor_set(v___x_424_, 0, v_x_401_);
v___x_431_ = v___x_424_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_x_401_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_x_402_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
v___y_416_ = v___x_431_;
goto v___jp_415_;
}
}
}
}
case 1:
{
lean_object* v_node_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_446_; 
v_node_434_ = lean_ctor_get(v_v_412_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_v_412_);
if (v_isSharedCheck_446_ == 0)
{
v___x_436_ = v_v_412_;
v_isShared_437_ = v_isSharedCheck_446_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_node_434_);
lean_dec(v_v_412_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_446_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_438_ = ((size_t)5ULL);
v___x_439_ = lean_usize_shift_right(v_x_399_, v___x_438_);
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_add(v_x_400_, v___x_440_);
v___x_442_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_396_, v_inst_397_, v_node_434_, v___x_439_, v___x_441_, v_x_401_, v_x_402_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_442_);
v___x_444_ = v___x_436_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
v___y_416_ = v___x_444_;
goto v___jp_415_;
}
}
}
default: 
{
lean_object* v___x_447_; 
lean_dec_ref(v_inst_397_);
lean_dec_ref(v_inst_396_);
v___x_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_447_, 0, v_x_401_);
lean_ctor_set(v___x_447_, 1, v_x_402_);
v___y_416_ = v___x_447_;
goto v___jp_415_;
}
}
v___jp_415_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_array_fset(v_xs_x27_414_, v_j_406_, v___y_416_);
lean_dec(v_j_406_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_417_);
v___x_419_ = v___x_410_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
else
{
lean_object* v_ks_450_; lean_object* v_vs_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_469_; 
v_ks_450_ = lean_ctor_get(v_x_398_, 0);
v_vs_451_ = lean_ctor_get(v_x_398_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_469_ == 0)
{
v___x_453_ = v_x_398_;
v_isShared_454_ = v_isSharedCheck_469_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_vs_451_);
lean_inc(v_ks_450_);
lean_dec(v_x_398_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_469_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_456_; 
if (v_isShared_454_ == 0)
{
v___x_456_ = v___x_453_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_ks_450_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_vs_451_);
v___x_456_ = v_reuseFailAlloc_468_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v_val_457_; size_t v___x_458_; uint8_t v___x_459_; 
lean_inc_ref(v_inst_396_);
v_val_457_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(v_inst_396_, v___x_456_, v_x_401_, v_x_402_);
v___x_458_ = ((size_t)7ULL);
v___x_459_ = lean_usize_dec_le(v___x_458_, v_x_400_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_val_457_);
v___x_461_ = lean_unsigned_to_nat(4u);
v___x_462_ = lean_nat_dec_lt(v___x_460_, v___x_461_);
lean_dec(v___x_460_);
if (v___x_462_ == 0)
{
lean_object* v_ks_463_; lean_object* v_vs_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_ks_463_ = lean_ctor_get(v_val_457_, 0);
lean_inc_ref(v_ks_463_);
v_vs_464_ = lean_ctor_get(v_val_457_, 1);
lean_inc_ref(v_vs_464_);
lean_dec_ref(v_val_457_);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntries___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntries___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntries___closed__0);
v___x_467_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_396_, v_inst_397_, v_x_400_, v_ks_463_, v_vs_464_, v___x_465_, v___x_466_);
lean_dec_ref(v_vs_464_);
lean_dec_ref(v_ks_463_);
return v___x_467_;
}
else
{
lean_dec_ref(v_inst_397_);
lean_dec_ref(v_inst_396_);
return v_val_457_;
}
}
else
{
lean_dec_ref(v_inst_397_);
lean_dec_ref(v_inst_396_);
return v_val_457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(lean_object* v_inst_470_, lean_object* v_inst_471_, size_t v_depth_472_, lean_object* v_keys_473_, lean_object* v_vals_474_, lean_object* v_i_475_, lean_object* v_entries_476_){
_start:
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_array_get_size(v_keys_473_);
v___x_478_ = lean_nat_dec_lt(v_i_475_, v___x_477_);
if (v___x_478_ == 0)
{
lean_dec(v_i_475_);
lean_dec_ref(v_inst_471_);
lean_dec_ref(v_inst_470_);
return v_entries_476_;
}
else
{
lean_object* v_k_479_; lean_object* v_v_480_; lean_object* v___x_481_; uint64_t v___x_482_; size_t v_h_483_; size_t v___x_484_; lean_object* v___x_485_; size_t v___x_486_; size_t v___x_487_; size_t v___x_488_; size_t v_h_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_k_479_ = lean_array_fget_borrowed(v_keys_473_, v_i_475_);
v_v_480_ = lean_array_fget_borrowed(v_vals_474_, v_i_475_);
lean_inc_ref_n(v_inst_471_, 2);
lean_inc_n(v_k_479_, 2);
v___x_481_ = lean_apply_1(v_inst_471_, v_k_479_);
v___x_482_ = lean_unbox_uint64(v___x_481_);
lean_dec_ref(v___x_481_);
v_h_483_ = lean_uint64_to_usize(v___x_482_);
v___x_484_ = ((size_t)5ULL);
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_sub(v_depth_472_, v___x_486_);
v___x_488_ = lean_usize_mul(v___x_484_, v___x_487_);
v_h_489_ = lean_usize_shift_right(v_h_483_, v___x_488_);
v___x_490_ = lean_nat_add(v_i_475_, v___x_485_);
lean_dec(v_i_475_);
lean_inc(v_v_480_);
lean_inc_ref(v_inst_470_);
v___x_491_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_470_, v_inst_471_, v_entries_476_, v_h_489_, v_depth_472_, v_k_479_, v_v_480_);
v_i_475_ = v___x_490_;
v_entries_476_ = v___x_491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg___boxed(lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_depth_495_, lean_object* v_keys_496_, lean_object* v_vals_497_, lean_object* v_i_498_, lean_object* v_entries_499_){
_start:
{
size_t v_depth_boxed_500_; lean_object* v_res_501_; 
v_depth_boxed_500_ = lean_unbox_usize(v_depth_495_);
lean_dec(v_depth_495_);
v_res_501_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_493_, v_inst_494_, v_depth_boxed_500_, v_keys_496_, v_vals_497_, v_i_498_, v_entries_499_);
lean_dec_ref(v_vals_497_);
lean_dec_ref(v_keys_496_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg___boxed(lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_x_504_, lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
size_t v_x_394__boxed_509_; size_t v_x_395__boxed_510_; lean_object* v_res_511_; 
v_x_394__boxed_509_ = lean_unbox_usize(v_x_505_);
lean_dec(v_x_505_);
v_x_395__boxed_510_ = lean_unbox_usize(v_x_506_);
lean_dec(v_x_506_);
v_res_511_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_502_, v_inst_503_, v_x_504_, v_x_394__boxed_509_, v_x_395__boxed_510_, v_x_507_, v_x_508_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(lean_object* v_00_u03b1_512_, lean_object* v_00_u03b2_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, size_t v_depth_516_, lean_object* v_keys_517_, lean_object* v_vals_518_, lean_object* v_heq_519_, lean_object* v_i_520_, lean_object* v_entries_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_514_, v_inst_515_, v_depth_516_, v_keys_517_, v_vals_518_, v_i_520_, v_entries_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___boxed(lean_object* v_00_u03b1_523_, lean_object* v_00_u03b2_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_depth_527_, lean_object* v_keys_528_, lean_object* v_vals_529_, lean_object* v_heq_530_, lean_object* v_i_531_, lean_object* v_entries_532_){
_start:
{
size_t v_depth_boxed_533_; lean_object* v_res_534_; 
v_depth_boxed_533_ = lean_unbox_usize(v_depth_527_);
lean_dec(v_depth_527_);
v_res_534_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(v_00_u03b1_523_, v_00_u03b2_524_, v_inst_525_, v_inst_526_, v_depth_boxed_533_, v_keys_528_, v_vals_529_, v_heq_530_, v_i_531_, v_entries_532_);
lean_dec_ref(v_vals_529_);
lean_dec_ref(v_keys_528_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux(lean_object* v_00_u03b1_535_, lean_object* v_00_u03b2_536_, lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_x_539_, size_t v_x_540_, size_t v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_537_, v_inst_538_, v_x_539_, v_x_540_, v_x_541_, v_x_542_, v_x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___boxed(lean_object* v_00_u03b1_545_, lean_object* v_00_u03b2_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_x_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
size_t v_x_569__boxed_554_; size_t v_x_570__boxed_555_; lean_object* v_res_556_; 
v_x_569__boxed_554_ = lean_unbox_usize(v_x_550_);
lean_dec(v_x_550_);
v_x_570__boxed_555_ = lean_unbox_usize(v_x_551_);
lean_dec(v_x_551_);
v_res_556_ = l_Lean_PersistentHashMap_insertAux(v_00_u03b1_545_, v_00_u03b2_546_, v_inst_547_, v_inst_548_, v_x_549_, v_x_569__boxed_554_, v_x_570__boxed_555_, v_x_552_, v_x_553_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
lean_object* v___x_562_; uint64_t v___x_563_; size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
lean_inc_ref(v_x_558_);
lean_inc(v_x_560_);
v___x_562_ = lean_apply_1(v_x_558_, v_x_560_);
v___x_563_ = lean_unbox_uint64(v___x_562_);
lean_dec_ref(v___x_562_);
v___x_564_ = lean_uint64_to_usize(v___x_563_);
v___x_565_ = ((size_t)1ULL);
v___x_566_ = l_Lean_PersistentHashMap_insertAux___redArg(v_x_557_, v_x_558_, v_x_559_, v___x_564_, v___x_565_, v_x_560_, v_x_561_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert(lean_object* v_00_u03b1_567_, lean_object* v_00_u03b2_568_, lean_object* v_x_569_, lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_PersistentHashMap_insert___redArg(v_x_569_, v_x_570_, v_x_571_, v_x_572_, v_x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg(lean_object* v_inst_575_, lean_object* v_keys_576_, lean_object* v_vals_577_, lean_object* v_i_578_, lean_object* v_k_579_){
_start:
{
lean_object* v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_array_get_size(v_keys_576_);
v___x_581_ = lean_nat_dec_lt(v_i_578_, v___x_580_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec(v_k_579_);
lean_dec(v_i_578_);
lean_dec_ref(v_inst_575_);
v___x_582_ = lean_box(0);
return v___x_582_;
}
else
{
lean_object* v_k_x27_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v_k_x27_583_ = lean_array_fget_borrowed(v_keys_576_, v_i_578_);
lean_inc_ref(v_inst_575_);
lean_inc(v_k_x27_583_);
lean_inc(v_k_579_);
v___x_584_ = lean_apply_2(v_inst_575_, v_k_579_, v_k_x27_583_);
v___x_585_ = lean_unbox(v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_add(v_i_578_, v___x_586_);
lean_dec(v_i_578_);
v_i_578_ = v___x_587_;
goto _start;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec(v_k_579_);
lean_dec_ref(v_inst_575_);
v___x_589_ = lean_array_fget_borrowed(v_vals_577_, v_i_578_);
lean_dec(v_i_578_);
lean_inc(v___x_589_);
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
return v___x_590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg___boxed(lean_object* v_inst_591_, lean_object* v_keys_592_, lean_object* v_vals_593_, lean_object* v_i_594_, lean_object* v_k_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_591_, v_keys_592_, v_vals_593_, v_i_594_, v_k_595_);
lean_dec_ref(v_vals_593_);
lean_dec_ref(v_keys_592_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux(lean_object* v_00_u03b1_597_, lean_object* v_00_u03b2_598_, lean_object* v_inst_599_, lean_object* v_keys_600_, lean_object* v_vals_601_, lean_object* v_heq_602_, lean_object* v_i_603_, lean_object* v_k_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_599_, v_keys_600_, v_vals_601_, v_i_603_, v_k_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___boxed(lean_object* v_00_u03b1_606_, lean_object* v_00_u03b2_607_, lean_object* v_inst_608_, lean_object* v_keys_609_, lean_object* v_vals_610_, lean_object* v_heq_611_, lean_object* v_i_612_, lean_object* v_k_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_PersistentHashMap_findAtAux(v_00_u03b1_606_, v_00_u03b2_607_, v_inst_608_, v_keys_609_, v_vals_610_, v_heq_611_, v_i_612_, v_k_613_);
lean_dec_ref(v_vals_610_);
lean_dec_ref(v_keys_609_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg(lean_object* v_inst_615_, lean_object* v_x_616_, size_t v_x_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_object* v_es_619_; lean_object* v___x_620_; size_t v___x_621_; size_t v___x_622_; lean_object* v_j_623_; lean_object* v___x_624_; 
v_es_619_ = lean_ctor_get(v_x_616_, 0);
lean_inc_ref(v_es_619_);
lean_dec_ref_known(v_x_616_, 1);
v___x_620_ = lean_box(2);
v___x_621_ = ((size_t)31ULL);
v___x_622_ = lean_usize_land(v_x_617_, v___x_621_);
v_j_623_ = lean_usize_to_nat(v___x_622_);
v___x_624_ = lean_array_get(v___x_620_, v_es_619_, v_j_623_);
lean_dec(v_j_623_);
lean_dec_ref(v_es_619_);
switch(lean_obj_tag(v___x_624_))
{
case 0:
{
lean_object* v_key_625_; lean_object* v_val_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_key_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_key_625_);
v_val_626_ = lean_ctor_get(v___x_624_, 1);
lean_inc(v_val_626_);
lean_dec_ref_known(v___x_624_, 2);
v___x_627_ = lean_apply_2(v_inst_615_, v_x_618_, v_key_625_);
v___x_628_ = lean_unbox(v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; 
lean_dec(v_val_626_);
v___x_629_ = lean_box(0);
return v___x_629_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v_val_626_);
return v___x_630_;
}
}
case 1:
{
lean_object* v_node_631_; size_t v___x_632_; size_t v___x_633_; 
v_node_631_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_node_631_);
lean_dec_ref_known(v___x_624_, 1);
v___x_632_ = ((size_t)5ULL);
v___x_633_ = lean_usize_shift_right(v_x_617_, v___x_632_);
v_x_616_ = v_node_631_;
v_x_617_ = v___x_633_;
goto _start;
}
default: 
{
lean_object* v___x_635_; 
lean_dec(v_x_618_);
lean_dec_ref(v_inst_615_);
v___x_635_ = lean_box(0);
return v___x_635_;
}
}
}
else
{
lean_object* v_ks_636_; lean_object* v_vs_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v_ks_636_ = lean_ctor_get(v_x_616_, 0);
lean_inc_ref(v_ks_636_);
v_vs_637_ = lean_ctor_get(v_x_616_, 1);
lean_inc_ref(v_vs_637_);
lean_dec_ref_known(v_x_616_, 2);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_615_, v_ks_636_, v_vs_637_, v___x_638_, v_x_618_);
lean_dec_ref(v_vs_637_);
lean_dec_ref(v_ks_636_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg___boxed(lean_object* v_inst_640_, lean_object* v_x_641_, lean_object* v_x_642_, lean_object* v_x_643_){
_start:
{
size_t v_x_118__boxed_644_; lean_object* v_res_645_; 
v_x_118__boxed_644_ = lean_unbox_usize(v_x_642_);
lean_dec(v_x_642_);
v_res_645_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_640_, v_x_641_, v_x_118__boxed_644_, v_x_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux(lean_object* v_00_u03b1_646_, lean_object* v_00_u03b2_647_, lean_object* v_inst_648_, lean_object* v_x_649_, size_t v_x_650_, lean_object* v_x_651_){
_start:
{
lean_object* v___x_652_; 
lean_inc_ref(v_x_649_);
v___x_652_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_648_, v_x_649_, v_x_650_, v_x_651_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___boxed(lean_object* v_00_u03b1_653_, lean_object* v_00_u03b2_654_, lean_object* v_inst_655_, lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_){
_start:
{
size_t v_x_170__boxed_659_; lean_object* v_res_660_; 
v_x_170__boxed_659_ = lean_unbox_usize(v_x_657_);
lean_dec(v_x_657_);
v_res_660_ = l_Lean_PersistentHashMap_findAux(v_00_u03b1_653_, v_00_u03b2_654_, v_inst_655_, v_x_656_, v_x_170__boxed_659_, v_x_658_);
lean_dec_ref(v_x_656_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
lean_object* v___x_665_; uint64_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
lean_inc(v_x_664_);
v___x_665_ = lean_apply_1(v_x_662_, v_x_664_);
v___x_666_ = lean_unbox_uint64(v___x_665_);
lean_dec_ref(v___x_665_);
v___x_667_ = lean_uint64_to_usize(v___x_666_);
lean_inc_ref(v_x_663_);
v___x_668_ = l_Lean_PersistentHashMap_findAux___redArg(v_x_661_, v_x_663_, v___x_667_, v_x_664_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg___boxed(lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_669_, v_x_670_, v_x_671_, v_x_672_);
lean_dec_ref(v_x_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_676_, v_x_677_, v_x_678_, v_x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___boxed(lean_object* v_00_u03b1_681_, lean_object* v_00_u03b2_682_, lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_PersistentHashMap_find_x3f(v_00_u03b1_681_, v_00_u03b2_682_, v_x_683_, v_x_684_, v_x_685_, v_x_686_);
lean_dec_ref(v_x_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(lean_object* v_x_688_, lean_object* v_x_689_, lean_object* v_m_690_, lean_object* v_i_691_, lean_object* v_x_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_688_, v_x_689_, v_m_690_, v_i_691_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed(lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_m_696_, lean_object* v_i_697_, lean_object* v_x_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(v_x_694_, v_x_695_, v_m_696_, v_i_697_, v_x_698_);
lean_dec_ref(v_m_696_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg(lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
lean_object* v___f_702_; 
v___f_702_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_702_, 0, v_x_700_);
lean_closure_set(v___f_702_, 1, v_x_701_);
return v___f_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
lean_object* v___f_707_; 
v___f_707_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_707_, 0, v_x_705_);
lean_closure_set(v___f_707_, 1, v_x_706_);
return v___f_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg(lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_m_710_, lean_object* v_a_711_, lean_object* v_b_u2080_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_708_, v_x_709_, v_m_710_, v_a_711_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_inc(v_b_u2080_712_);
return v_b_u2080_712_;
}
else
{
lean_object* v_val_714_; 
v_val_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_val_714_);
lean_dec_ref_known(v___x_713_, 1);
return v_val_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg___boxed(lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_m_717_, lean_object* v_a_718_, lean_object* v_b_u2080_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_PersistentHashMap_findD___redArg(v_x_715_, v_x_716_, v_m_717_, v_a_718_, v_b_u2080_719_);
lean_dec(v_b_u2080_719_);
lean_dec_ref(v_m_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD(lean_object* v_00_u03b1_721_, lean_object* v_00_u03b2_722_, lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_m_725_, lean_object* v_a_726_, lean_object* v_b_u2080_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_723_, v_x_724_, v_m_725_, v_a_726_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_inc(v_b_u2080_727_);
return v_b_u2080_727_;
}
else
{
lean_object* v_val_729_; 
v_val_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_val_729_);
lean_dec_ref_known(v___x_728_, 1);
return v_val_729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___boxed(lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_m_734_, lean_object* v_a_735_, lean_object* v_b_u2080_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l_Lean_PersistentHashMap_findD(v_00_u03b1_730_, v_00_u03b2_731_, v_x_732_, v_x_733_, v_m_734_, v_a_735_, v_b_u2080_736_);
lean_dec(v_b_u2080_736_);
lean_dec_ref(v_m_734_);
return v_res_737_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_741_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__2));
v___x_742_ = lean_unsigned_to_nat(14u);
v___x_743_ = lean_unsigned_to_nat(178u);
v___x_744_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__1));
v___x_745_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__0));
v___x_746_ = l_mkPanicMessageWithDecl(v___x_745_, v___x_744_, v___x_743_, v___x_742_, v___x_741_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg(lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_inst_749_, lean_object* v_m_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_747_, v_x_748_, v_m_750_, v_a_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_754_ = l_panic___redArg(v_inst_749_, v___x_753_);
return v___x_754_;
}
else
{
lean_object* v_val_755_; 
v_val_755_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_val_755_);
lean_dec_ref_known(v___x_752_, 1);
return v_val_755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg___boxed(lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_inst_758_, lean_object* v_m_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_PersistentHashMap_find_x21___redArg(v_x_756_, v_x_757_, v_inst_758_, v_m_759_, v_a_760_);
lean_dec_ref(v_m_759_);
lean_dec(v_inst_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_inst_766_, lean_object* v_m_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_764_, v_x_765_, v_m_767_, v_a_768_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_771_ = l_panic___redArg(v_inst_766_, v___x_770_);
return v___x_771_;
}
else
{
lean_object* v_val_772_; 
v_val_772_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_val_772_);
lean_dec_ref_known(v___x_769_, 1);
return v_val_772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___boxed(lean_object* v_00_u03b1_773_, lean_object* v_00_u03b2_774_, lean_object* v_x_775_, lean_object* v_x_776_, lean_object* v_inst_777_, lean_object* v_m_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_PersistentHashMap_find_x21(v_00_u03b1_773_, v_00_u03b2_774_, v_x_775_, v_x_776_, v_inst_777_, v_m_778_, v_a_779_);
lean_dec_ref(v_m_778_);
lean_dec(v_inst_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg(lean_object* v_inst_781_, lean_object* v_keys_782_, lean_object* v_vals_783_, lean_object* v_i_784_, lean_object* v_k_785_){
_start:
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = lean_array_get_size(v_keys_782_);
v___x_787_ = lean_nat_dec_lt(v_i_784_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec(v_k_785_);
lean_dec(v_i_784_);
lean_dec_ref(v_inst_781_);
v___x_788_ = lean_box(0);
return v___x_788_;
}
else
{
lean_object* v_k_x27_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_k_x27_789_ = lean_array_fget_borrowed(v_keys_782_, v_i_784_);
lean_inc_ref(v_inst_781_);
lean_inc(v_k_x27_789_);
lean_inc(v_k_785_);
v___x_790_ = lean_apply_2(v_inst_781_, v_k_785_, v_k_x27_789_);
v___x_791_ = lean_unbox(v___x_790_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v_i_784_, v___x_792_);
lean_dec(v_i_784_);
v_i_784_ = v___x_793_;
goto _start;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec(v_k_785_);
lean_dec_ref(v_inst_781_);
v___x_795_ = lean_array_fget_borrowed(v_vals_783_, v_i_784_);
lean_dec(v_i_784_);
lean_inc(v___x_795_);
lean_inc(v_k_x27_789_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v_k_x27_789_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg___boxed(lean_object* v_inst_798_, lean_object* v_keys_799_, lean_object* v_vals_800_, lean_object* v_i_801_, lean_object* v_k_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_798_, v_keys_799_, v_vals_800_, v_i_801_, v_k_802_);
lean_dec_ref(v_vals_800_);
lean_dec_ref(v_keys_799_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux(lean_object* v_00_u03b1_804_, lean_object* v_00_u03b2_805_, lean_object* v_inst_806_, lean_object* v_keys_807_, lean_object* v_vals_808_, lean_object* v_heq_809_, lean_object* v_i_810_, lean_object* v_k_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_806_, v_keys_807_, v_vals_808_, v_i_810_, v_k_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___boxed(lean_object* v_00_u03b1_813_, lean_object* v_00_u03b2_814_, lean_object* v_inst_815_, lean_object* v_keys_816_, lean_object* v_vals_817_, lean_object* v_heq_818_, lean_object* v_i_819_, lean_object* v_k_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_PersistentHashMap_findEntryAtAux(v_00_u03b1_813_, v_00_u03b2_814_, v_inst_815_, v_keys_816_, v_vals_817_, v_heq_818_, v_i_819_, v_k_820_);
lean_dec_ref(v_vals_817_);
lean_dec_ref(v_keys_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg(lean_object* v_inst_822_, lean_object* v_x_823_, size_t v_x_824_, lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_823_) == 0)
{
lean_object* v_es_826_; lean_object* v___x_827_; size_t v___x_828_; size_t v___x_829_; lean_object* v_j_830_; lean_object* v___x_831_; 
v_es_826_ = lean_ctor_get(v_x_823_, 0);
lean_inc_ref(v_es_826_);
lean_dec_ref_known(v_x_823_, 1);
v___x_827_ = lean_box(2);
v___x_828_ = ((size_t)31ULL);
v___x_829_ = lean_usize_land(v_x_824_, v___x_828_);
v_j_830_ = lean_usize_to_nat(v___x_829_);
v___x_831_ = lean_array_get(v___x_827_, v_es_826_, v_j_830_);
lean_dec(v_j_830_);
lean_dec_ref(v_es_826_);
switch(lean_obj_tag(v___x_831_))
{
case 0:
{
lean_object* v_key_832_; lean_object* v_val_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_key_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc_n(v_key_832_, 2);
v_val_833_ = lean_ctor_get(v___x_831_, 1);
lean_inc(v_val_833_);
lean_dec_ref_known(v___x_831_, 2);
v___x_834_ = lean_apply_2(v_inst_822_, v_x_825_, v_key_832_);
v___x_835_ = lean_unbox(v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_dec(v_val_833_);
lean_dec(v_key_832_);
v___x_836_ = lean_box(0);
return v___x_836_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v_key_832_);
lean_ctor_set(v___x_837_, 1, v_val_833_);
v___x_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
case 1:
{
lean_object* v_node_839_; size_t v___x_840_; size_t v___x_841_; 
v_node_839_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_node_839_);
lean_dec_ref_known(v___x_831_, 1);
v___x_840_ = ((size_t)5ULL);
v___x_841_ = lean_usize_shift_right(v_x_824_, v___x_840_);
v_x_823_ = v_node_839_;
v_x_824_ = v___x_841_;
goto _start;
}
default: 
{
lean_object* v___x_843_; 
lean_dec(v_x_825_);
lean_dec_ref(v_inst_822_);
v___x_843_ = lean_box(0);
return v___x_843_;
}
}
}
else
{
lean_object* v_ks_844_; lean_object* v_vs_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v_ks_844_ = lean_ctor_get(v_x_823_, 0);
lean_inc_ref(v_ks_844_);
v_vs_845_ = lean_ctor_get(v_x_823_, 1);
lean_inc_ref(v_vs_845_);
lean_dec_ref_known(v_x_823_, 2);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_822_, v_ks_844_, v_vs_845_, v___x_846_, v_x_825_);
lean_dec_ref(v_vs_845_);
lean_dec_ref(v_ks_844_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg___boxed(lean_object* v_inst_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
size_t v_x_121__boxed_852_; lean_object* v_res_853_; 
v_x_121__boxed_852_ = lean_unbox_usize(v_x_850_);
lean_dec(v_x_850_);
v_res_853_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_848_, v_x_849_, v_x_121__boxed_852_, v_x_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux(lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_inst_856_, lean_object* v_x_857_, size_t v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v___x_860_; 
lean_inc_ref(v_x_857_);
v___x_860_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_856_, v_x_857_, v_x_858_, v_x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___boxed(lean_object* v_00_u03b1_861_, lean_object* v_00_u03b2_862_, lean_object* v_inst_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
size_t v_x_175__boxed_867_; lean_object* v_res_868_; 
v_x_175__boxed_867_ = lean_unbox_usize(v_x_865_);
lean_dec(v_x_865_);
v_res_868_ = l_Lean_PersistentHashMap_findEntryAux(v_00_u03b1_861_, v_00_u03b2_862_, v_inst_863_, v_x_864_, v_x_175__boxed_867_, v_x_866_);
lean_dec_ref(v_x_864_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object* v_x_869_, lean_object* v_x_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
lean_object* v___x_873_; uint64_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
lean_inc(v_x_872_);
v___x_873_ = lean_apply_1(v_x_870_, v_x_872_);
v___x_874_ = lean_unbox_uint64(v___x_873_);
lean_dec_ref(v___x_873_);
v___x_875_ = lean_uint64_to_usize(v___x_874_);
lean_inc_ref(v_x_871_);
v___x_876_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_x_869_, v_x_871_, v___x_875_, v_x_872_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg___boxed(lean_object* v_x_877_, lean_object* v_x_878_, lean_object* v_x_879_, lean_object* v_x_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_877_, v_x_878_, v_x_879_, v_x_880_);
lean_dec_ref(v_x_879_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f(lean_object* v_00_u03b1_882_, lean_object* v_00_u03b2_883_, lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_884_, v_x_885_, v_x_886_, v_x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___boxed(lean_object* v_00_u03b1_889_, lean_object* v_00_u03b2_890_, lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v_x_893_, lean_object* v_x_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_PersistentHashMap_findEntry_x3f(v_00_u03b1_889_, v_00_u03b2_890_, v_x_891_, v_x_892_, v_x_893_, v_x_894_);
lean_dec_ref(v_x_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg(lean_object* v_inst_896_, lean_object* v_keys_897_, lean_object* v_i_898_, lean_object* v_k_899_, lean_object* v_k_u2080_900_){
_start:
{
lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_901_ = lean_array_get_size(v_keys_897_);
v___x_902_ = lean_nat_dec_lt(v_i_898_, v___x_901_);
if (v___x_902_ == 0)
{
lean_dec(v_k_899_);
lean_dec(v_i_898_);
lean_dec_ref(v_inst_896_);
lean_inc(v_k_u2080_900_);
return v_k_u2080_900_;
}
else
{
lean_object* v_k_x27_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_k_x27_903_ = lean_array_fget_borrowed(v_keys_897_, v_i_898_);
lean_inc_ref(v_inst_896_);
lean_inc(v_k_x27_903_);
lean_inc(v_k_899_);
v___x_904_ = lean_apply_2(v_inst_896_, v_k_899_, v_k_x27_903_);
v___x_905_ = lean_unbox(v___x_904_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_nat_add(v_i_898_, v___x_906_);
lean_dec(v_i_898_);
v_i_898_ = v___x_907_;
goto _start;
}
else
{
lean_dec(v_k_899_);
lean_dec(v_i_898_);
lean_dec_ref(v_inst_896_);
lean_inc(v_k_x27_903_);
return v_k_x27_903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg___boxed(lean_object* v_inst_909_, lean_object* v_keys_910_, lean_object* v_i_911_, lean_object* v_k_912_, lean_object* v_k_u2080_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_909_, v_keys_910_, v_i_911_, v_k_912_, v_k_u2080_913_);
lean_dec(v_k_u2080_913_);
lean_dec_ref(v_keys_910_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux(lean_object* v_00_u03b1_915_, lean_object* v_00_u03b2_916_, lean_object* v_inst_917_, lean_object* v_keys_918_, lean_object* v_vals_919_, lean_object* v_heq_920_, lean_object* v_i_921_, lean_object* v_k_922_, lean_object* v_k_u2080_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_917_, v_keys_918_, v_i_921_, v_k_922_, v_k_u2080_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___boxed(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_inst_927_, lean_object* v_keys_928_, lean_object* v_vals_929_, lean_object* v_heq_930_, lean_object* v_i_931_, lean_object* v_k_932_, lean_object* v_k_u2080_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_PersistentHashMap_findKeyDAtAux(v_00_u03b1_925_, v_00_u03b2_926_, v_inst_927_, v_keys_928_, v_vals_929_, v_heq_930_, v_i_931_, v_k_932_, v_k_u2080_933_);
lean_dec(v_k_u2080_933_);
lean_dec_ref(v_vals_929_);
lean_dec_ref(v_keys_928_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object* v_inst_935_, lean_object* v_x_936_, size_t v_x_937_, lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
if (lean_obj_tag(v_x_936_) == 0)
{
lean_object* v_es_940_; lean_object* v___x_941_; size_t v___x_942_; size_t v___x_943_; lean_object* v_j_944_; lean_object* v___x_945_; 
v_es_940_ = lean_ctor_get(v_x_936_, 0);
lean_inc_ref(v_es_940_);
lean_dec_ref_known(v_x_936_, 1);
v___x_941_ = lean_box(2);
v___x_942_ = ((size_t)31ULL);
v___x_943_ = lean_usize_land(v_x_937_, v___x_942_);
v_j_944_ = lean_usize_to_nat(v___x_943_);
v___x_945_ = lean_array_get(v___x_941_, v_es_940_, v_j_944_);
lean_dec(v_j_944_);
lean_dec_ref(v_es_940_);
switch(lean_obj_tag(v___x_945_))
{
case 0:
{
lean_object* v_key_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_key_946_ = lean_ctor_get(v___x_945_, 0);
lean_inc_n(v_key_946_, 2);
lean_dec_ref_known(v___x_945_, 2);
v___x_947_ = lean_apply_2(v_inst_935_, v_x_938_, v_key_946_);
v___x_948_ = lean_unbox(v___x_947_);
if (v___x_948_ == 0)
{
lean_dec(v_key_946_);
lean_inc(v_x_939_);
return v_x_939_;
}
else
{
return v_key_946_;
}
}
case 1:
{
lean_object* v_node_949_; size_t v___x_950_; size_t v___x_951_; 
v_node_949_ = lean_ctor_get(v___x_945_, 0);
lean_inc(v_node_949_);
lean_dec_ref_known(v___x_945_, 1);
v___x_950_ = ((size_t)5ULL);
v___x_951_ = lean_usize_shift_right(v_x_937_, v___x_950_);
v_x_936_ = v_node_949_;
v_x_937_ = v___x_951_;
goto _start;
}
default: 
{
lean_dec(v_x_938_);
lean_dec_ref(v_inst_935_);
lean_inc(v_x_939_);
return v_x_939_;
}
}
}
else
{
lean_object* v_ks_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_ks_953_ = lean_ctor_get(v_x_936_, 0);
lean_inc_ref(v_ks_953_);
lean_dec_ref_known(v_x_936_, 2);
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_935_, v_ks_953_, v___x_954_, v_x_938_, v_x_939_);
lean_dec_ref(v_ks_953_);
return v___x_955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg___boxed(lean_object* v_inst_956_, lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
size_t v_x_113__boxed_961_; lean_object* v_res_962_; 
v_x_113__boxed_961_ = lean_unbox_usize(v_x_958_);
lean_dec(v_x_958_);
v_res_962_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_956_, v_x_957_, v_x_113__boxed_961_, v_x_959_, v_x_960_);
lean_dec(v_x_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux(lean_object* v_00_u03b1_963_, lean_object* v_00_u03b2_964_, lean_object* v_inst_965_, lean_object* v_x_966_, size_t v_x_967_, lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
lean_object* v___x_970_; 
v___x_970_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_965_, v_x_966_, v_x_967_, v_x_968_, v_x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___boxed(lean_object* v_00_u03b1_971_, lean_object* v_00_u03b2_972_, lean_object* v_inst_973_, lean_object* v_x_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
size_t v_x_160__boxed_978_; lean_object* v_res_979_; 
v_x_160__boxed_978_ = lean_unbox_usize(v_x_975_);
lean_dec(v_x_975_);
v_res_979_ = l_Lean_PersistentHashMap_findKeyDAux(v_00_u03b1_971_, v_00_u03b2_972_, v_inst_973_, v_x_974_, v_x_160__boxed_978_, v_x_976_, v_x_977_);
lean_dec(v_x_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg(lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_m_982_, lean_object* v_a_983_, lean_object* v_a_u2080_984_){
_start:
{
lean_object* v___x_985_; uint64_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
lean_inc(v_a_983_);
v___x_985_ = lean_apply_1(v_x_981_, v_a_983_);
v___x_986_ = lean_unbox_uint64(v___x_985_);
lean_dec_ref(v___x_985_);
v___x_987_ = lean_uint64_to_usize(v___x_986_);
v___x_988_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_980_, v_m_982_, v___x_987_, v_a_983_, v_a_u2080_984_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg___boxed(lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_m_991_, lean_object* v_a_992_, lean_object* v_a_u2080_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_PersistentHashMap_findKeyD___redArg(v_x_989_, v_x_990_, v_m_991_, v_a_992_, v_a_u2080_993_);
lean_dec(v_a_u2080_993_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD(lean_object* v_00_u03b1_995_, lean_object* v_00_u03b2_996_, lean_object* v_x_997_, lean_object* v_x_998_, lean_object* v_m_999_, lean_object* v_a_1000_, lean_object* v_a_u2080_1001_){
_start:
{
lean_object* v___x_1002_; uint64_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
lean_inc(v_a_1000_);
v___x_1002_ = lean_apply_1(v_x_998_, v_a_1000_);
v___x_1003_ = lean_unbox_uint64(v___x_1002_);
lean_dec_ref(v___x_1002_);
v___x_1004_ = lean_uint64_to_usize(v___x_1003_);
v___x_1005_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_997_, v_m_999_, v___x_1004_, v_a_1000_, v_a_u2080_1001_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___boxed(lean_object* v_00_u03b1_1006_, lean_object* v_00_u03b2_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_, lean_object* v_m_1010_, lean_object* v_a_1011_, lean_object* v_a_u2080_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_PersistentHashMap_findKeyD(v_00_u03b1_1006_, v_00_u03b2_1007_, v_x_1008_, v_x_1009_, v_m_1010_, v_a_1011_, v_a_u2080_1012_);
lean_dec(v_a_u2080_1012_);
return v_res_1013_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___redArg(lean_object* v_inst_1014_, lean_object* v_keys_1015_, lean_object* v_i_1016_, lean_object* v_k_1017_){
_start:
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_array_get_size(v_keys_1015_);
v___x_1019_ = lean_nat_dec_lt(v_i_1016_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_dec(v_k_1017_);
lean_dec(v_i_1016_);
lean_dec_ref(v_inst_1014_);
return v___x_1019_;
}
else
{
lean_object* v_k_x27_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_k_x27_1020_ = lean_array_fget_borrowed(v_keys_1015_, v_i_1016_);
lean_inc_ref(v_inst_1014_);
lean_inc(v_k_x27_1020_);
lean_inc(v_k_1017_);
v___x_1021_ = lean_apply_2(v_inst_1014_, v_k_1017_, v_k_x27_1020_);
v___x_1022_ = lean_unbox(v___x_1021_);
if (v___x_1022_ == 0)
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_nat_add(v_i_1016_, v___x_1023_);
lean_dec(v_i_1016_);
v_i_1016_ = v___x_1024_;
goto _start;
}
else
{
lean_dec(v_k_1017_);
lean_dec(v_i_1016_);
lean_dec_ref(v_inst_1014_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___redArg___boxed(lean_object* v_inst_1026_, lean_object* v_keys_1027_, lean_object* v_i_1028_, lean_object* v_k_1029_){
_start:
{
uint8_t v_res_1030_; lean_object* v_r_1031_; 
v_res_1030_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1026_, v_keys_1027_, v_i_1028_, v_k_1029_);
lean_dec_ref(v_keys_1027_);
v_r_1031_ = lean_box(v_res_1030_);
return v_r_1031_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux(lean_object* v_00_u03b1_1032_, lean_object* v_00_u03b2_1033_, lean_object* v_inst_1034_, lean_object* v_keys_1035_, lean_object* v_vals_1036_, lean_object* v_heq_1037_, lean_object* v_i_1038_, lean_object* v_k_1039_){
_start:
{
uint8_t v___x_1040_; 
v___x_1040_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1034_, v_keys_1035_, v_i_1038_, v_k_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_00_u03b2_1042_, lean_object* v_inst_1043_, lean_object* v_keys_1044_, lean_object* v_vals_1045_, lean_object* v_heq_1046_, lean_object* v_i_1047_, lean_object* v_k_1048_){
_start:
{
uint8_t v_res_1049_; lean_object* v_r_1050_; 
v_res_1049_ = l_Lean_PersistentHashMap_containsAtAux(v_00_u03b1_1041_, v_00_u03b2_1042_, v_inst_1043_, v_keys_1044_, v_vals_1045_, v_heq_1046_, v_i_1047_, v_k_1048_);
lean_dec_ref(v_vals_1045_);
lean_dec_ref(v_keys_1044_);
v_r_1050_ = lean_box(v_res_1049_);
return v_r_1050_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___redArg(lean_object* v_inst_1051_, lean_object* v_x_1052_, size_t v_x_1053_, lean_object* v_x_1054_){
_start:
{
if (lean_obj_tag(v_x_1052_) == 0)
{
lean_object* v_es_1055_; lean_object* v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; lean_object* v_j_1059_; lean_object* v___x_1060_; 
v_es_1055_ = lean_ctor_get(v_x_1052_, 0);
lean_inc_ref(v_es_1055_);
lean_dec_ref_known(v_x_1052_, 1);
v___x_1056_ = lean_box(2);
v___x_1057_ = ((size_t)31ULL);
v___x_1058_ = lean_usize_land(v_x_1053_, v___x_1057_);
v_j_1059_ = lean_usize_to_nat(v___x_1058_);
v___x_1060_ = lean_array_get(v___x_1056_, v_es_1055_, v_j_1059_);
lean_dec(v_j_1059_);
lean_dec_ref(v_es_1055_);
switch(lean_obj_tag(v___x_1060_))
{
case 0:
{
lean_object* v_key_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_key_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_key_1061_);
lean_dec_ref_known(v___x_1060_, 2);
v___x_1062_ = lean_apply_2(v_inst_1051_, v_x_1054_, v_key_1061_);
v___x_1063_ = lean_unbox(v___x_1062_);
return v___x_1063_;
}
case 1:
{
lean_object* v_node_1064_; size_t v___x_1065_; size_t v___x_1066_; 
v_node_1064_ = lean_ctor_get(v___x_1060_, 0);
lean_inc(v_node_1064_);
lean_dec_ref_known(v___x_1060_, 1);
v___x_1065_ = ((size_t)5ULL);
v___x_1066_ = lean_usize_shift_right(v_x_1053_, v___x_1065_);
v_x_1052_ = v_node_1064_;
v_x_1053_ = v___x_1066_;
goto _start;
}
default: 
{
uint8_t v___x_1068_; 
lean_dec(v_x_1054_);
lean_dec_ref(v_inst_1051_);
v___x_1068_ = 0;
return v___x_1068_;
}
}
}
else
{
lean_object* v_ks_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_ks_1069_ = lean_ctor_get(v_x_1052_, 0);
lean_inc_ref(v_ks_1069_);
lean_dec_ref_known(v_x_1052_, 2);
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1051_, v_ks_1069_, v___x_1070_, v_x_1054_);
lean_dec_ref(v_ks_1069_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___redArg___boxed(lean_object* v_inst_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
size_t v_x_104__boxed_1076_; uint8_t v_res_1077_; lean_object* v_r_1078_; 
v_x_104__boxed_1076_ = lean_unbox_usize(v_x_1074_);
lean_dec(v_x_1074_);
v_res_1077_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1072_, v_x_1073_, v_x_104__boxed_1076_, v_x_1075_);
v_r_1078_ = lean_box(v_res_1077_);
return v_r_1078_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux(lean_object* v_00_u03b1_1079_, lean_object* v_00_u03b2_1080_, lean_object* v_inst_1081_, lean_object* v_x_1082_, size_t v_x_1083_, lean_object* v_x_1084_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1081_, v_x_1082_, v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___boxed(lean_object* v_00_u03b1_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_inst_1088_, lean_object* v_x_1089_, lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
size_t v_x_150__boxed_1092_; uint8_t v_res_1093_; lean_object* v_r_1094_; 
v_x_150__boxed_1092_ = lean_unbox_usize(v_x_1090_);
lean_dec(v_x_1090_);
v_res_1093_ = l_Lean_PersistentHashMap_containsAux(v_00_u03b1_1086_, v_00_u03b2_1087_, v_inst_1088_, v_x_1089_, v_x_150__boxed_1092_, v_x_1091_);
v_r_1094_ = lean_box(v_res_1093_);
return v_r_1094_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v___x_1099_; uint64_t v___x_1100_; size_t v___x_1101_; uint8_t v___x_1102_; 
lean_inc(v_x_1098_);
v___x_1099_ = lean_apply_1(v_inst_1096_, v_x_1098_);
v___x_1100_ = lean_unbox_uint64(v___x_1099_);
lean_dec_ref(v___x_1099_);
v___x_1101_ = lean_uint64_to_usize(v___x_1100_);
v___x_1102_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1095_, v_x_1097_, v___x_1101_, v_x_1098_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___redArg___boxed(lean_object* v_inst_1103_, lean_object* v_inst_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_){
_start:
{
uint8_t v_res_1107_; lean_object* v_r_1108_; 
v_res_1107_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1103_, v_inst_1104_, v_x_1105_, v_x_1106_);
v_r_1108_ = lean_box(v_res_1107_);
return v_r_1108_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains(lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_inst_1111_, lean_object* v_inst_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
uint8_t v___x_1115_; 
v___x_1115_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1111_, v_inst_1112_, v_x_1113_, v_x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___boxed(lean_object* v_00_u03b1_1116_, lean_object* v_00_u03b2_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
uint8_t v_res_1122_; lean_object* v_r_1123_; 
v_res_1122_ = l_Lean_PersistentHashMap_contains(v_00_u03b1_1116_, v_00_u03b2_1117_, v_inst_1118_, v_inst_1119_, v_x_1120_, v_x_1121_);
v_r_1123_ = lean_box(v_res_1122_);
return v_r_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg(lean_object* v_a_1124_, lean_object* v_i_1125_, lean_object* v_acc_1126_){
_start:
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = lean_array_get_size(v_a_1124_);
v___x_1128_ = lean_nat_dec_lt(v_i_1125_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_dec(v_i_1125_);
return v_acc_1126_;
}
else
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_array_fget(v_a_1124_, v_i_1125_);
switch(lean_obj_tag(v___x_1129_))
{
case 0:
{
if (lean_obj_tag(v_acc_1126_) == 0)
{
lean_object* v_key_1130_; lean_object* v_val_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1142_; 
v_key_1130_ = lean_ctor_get(v___x_1129_, 0);
v_val_1131_ = lean_ctor_get(v___x_1129_, 1);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1133_ = v___x_1129_;
v_isShared_1134_ = v_isSharedCheck_1142_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_val_1131_);
lean_inc(v_key_1130_);
lean_dec(v___x_1129_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1142_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1135_ = lean_unsigned_to_nat(1u);
v___x_1136_ = lean_nat_add(v_i_1125_, v___x_1135_);
lean_dec(v_i_1125_);
if (v_isShared_1134_ == 0)
{
v___x_1138_ = v___x_1133_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_key_1130_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_val_1131_);
v___x_1138_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
v_i_1125_ = v___x_1136_;
v_acc_1126_ = v___x_1139_;
goto _start;
}
}
}
else
{
lean_object* v___x_1143_; 
lean_dec_ref_known(v_acc_1126_, 1);
lean_dec_ref_known(v___x_1129_, 2);
lean_dec(v_i_1125_);
v___x_1143_ = lean_box(0);
return v___x_1143_;
}
}
case 1:
{
lean_object* v___x_1144_; 
lean_dec_ref_known(v___x_1129_, 1);
lean_dec(v_acc_1126_);
lean_dec(v_i_1125_);
v___x_1144_ = lean_box(0);
return v___x_1144_;
}
default: 
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = lean_unsigned_to_nat(1u);
v___x_1146_ = lean_nat_add(v_i_1125_, v___x_1145_);
lean_dec(v_i_1125_);
v_i_1125_ = v___x_1146_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg___boxed(lean_object* v_a_1148_, lean_object* v_i_1149_, lean_object* v_acc_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1148_, v_i_1149_, v_acc_1150_);
lean_dec_ref(v_a_1148_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries(lean_object* v_00_u03b1_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_a_1154_, lean_object* v_i_1155_, lean_object* v_acc_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1154_, v_i_1155_, v_acc_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_00_u03b2_1159_, lean_object* v_a_1160_, lean_object* v_i_1161_, lean_object* v_acc_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_PersistentHashMap_isUnaryEntries(v_00_u03b1_1158_, v_00_u03b2_1159_, v_a_1160_, v_i_1161_, v_acc_1162_);
lean_dec_ref(v_a_1160_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object* v_x_1164_){
_start:
{
if (lean_obj_tag(v_x_1164_) == 0)
{
lean_object* v_es_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_es_1165_ = lean_ctor_get(v_x_1164_, 0);
lean_inc_ref(v_es_1165_);
lean_dec_ref_known(v_x_1164_, 1);
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = lean_box(0);
v___x_1168_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_es_1165_, v___x_1166_, v___x_1167_);
lean_dec_ref(v_es_1165_);
return v___x_1168_;
}
else
{
lean_object* v_ks_1169_; lean_object* v_vs_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1185_; 
v_ks_1169_ = lean_ctor_get(v_x_1164_, 0);
v_vs_1170_ = lean_ctor_get(v_x_1164_, 1);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_x_1164_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1172_ = v_x_1164_;
v_isShared_1173_ = v_isSharedCheck_1185_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_vs_1170_);
lean_inc(v_ks_1169_);
lean_dec(v_x_1164_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1185_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v___x_1174_ = lean_unsigned_to_nat(1u);
v___x_1175_ = lean_array_get_size(v_ks_1169_);
v___x_1176_ = lean_nat_dec_eq(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
lean_del_object(v___x_1172_);
lean_dec_ref(v_vs_1170_);
lean_dec_ref(v_ks_1169_);
v___x_1177_ = lean_box(0);
return v___x_1177_;
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1178_ = lean_unsigned_to_nat(0u);
v___x_1179_ = lean_array_fget(v_ks_1169_, v___x_1178_);
lean_dec_ref(v_ks_1169_);
v___x_1180_ = lean_array_fget(v_vs_1170_, v___x_1178_);
lean_dec_ref(v_vs_1170_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set_tag(v___x_1172_, 0);
lean_ctor_set(v___x_1172_, 1, v___x_1180_);
lean_ctor_set(v___x_1172_, 0, v___x_1179_);
v___x_1182_ = v___x_1172_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
return v___x_1183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode(lean_object* v_00_u03b1_1186_, lean_object* v_00_u03b2_1187_, lean_object* v_x_1188_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg(lean_object* v_inst_1190_, lean_object* v_x_1191_, size_t v_x_1192_, lean_object* v_x_1193_){
_start:
{
if (lean_obj_tag(v_x_1191_) == 0)
{
lean_object* v_es_1194_; lean_object* v___x_1195_; size_t v___x_1196_; size_t v___x_1197_; lean_object* v_j_1198_; lean_object* v_entry_1199_; 
v_es_1194_ = lean_ctor_get(v_x_1191_, 0);
v___x_1195_ = lean_box(2);
v___x_1196_ = ((size_t)31ULL);
v___x_1197_ = lean_usize_land(v_x_1192_, v___x_1196_);
v_j_1198_ = lean_usize_to_nat(v___x_1197_);
v_entry_1199_ = lean_array_get(v___x_1195_, v_es_1194_, v_j_1198_);
switch(lean_obj_tag(v_entry_1199_))
{
case 0:
{
lean_object* v_key_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v_key_1200_ = lean_ctor_get(v_entry_1199_, 0);
lean_inc(v_key_1200_);
lean_dec_ref_known(v_entry_1199_, 2);
v___x_1201_ = lean_apply_2(v_inst_1190_, v_x_1193_, v_key_1200_);
v___x_1202_ = lean_unbox(v___x_1201_);
if (v___x_1202_ == 0)
{
lean_dec(v_j_1198_);
return v_x_1191_;
}
else
{
lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1210_; 
lean_inc_ref(v_es_1194_);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; 
v_unused_1211_ = lean_ctor_get(v_x_1191_, 0);
lean_dec(v_unused_1211_);
v___x_1204_ = v_x_1191_;
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
else
{
lean_dec(v_x_1191_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1210_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = lean_array_set(v_es_1194_, v_j_1198_, v___x_1195_);
lean_dec(v_j_1198_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1206_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
case 1:
{
lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1246_; 
lean_inc_ref(v_es_1194_);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v_x_1191_, 0);
lean_dec(v_unused_1247_);
v___x_1213_ = v_x_1191_;
v_isShared_1214_ = v_isSharedCheck_1246_;
goto v_resetjp_1212_;
}
else
{
lean_dec(v_x_1191_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1246_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_node_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1245_; 
v_node_1215_ = lean_ctor_get(v_entry_1199_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_entry_1199_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1217_ = v_entry_1199_;
v_isShared_1218_ = v_isSharedCheck_1245_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_node_1215_);
lean_dec(v_entry_1199_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1245_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
size_t v___x_1219_; lean_object* v_entries_1220_; size_t v___x_1221_; lean_object* v_newNode_1222_; lean_object* v___x_1223_; 
v___x_1219_ = ((size_t)5ULL);
v_entries_1220_ = lean_array_set(v_es_1194_, v_j_1198_, v___x_1195_);
v___x_1221_ = lean_usize_shift_right(v_x_1192_, v___x_1219_);
v_newNode_1222_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1190_, v_node_1215_, v___x_1221_, v_x_1193_);
lean_inc_ref(v_newNode_1222_);
v___x_1223_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1222_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v___x_1225_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v_newNode_1222_);
v___x_1225_ = v___x_1217_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_newNode_1222_);
v___x_1225_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1226_ = lean_array_set(v_entries_1220_, v_j_1198_, v___x_1225_);
lean_dec(v_j_1198_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1226_);
v___x_1228_ = v___x_1213_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
else
{
lean_object* v_val_1231_; lean_object* v_fst_1232_; lean_object* v_snd_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1244_; 
lean_dec_ref(v_newNode_1222_);
lean_del_object(v___x_1217_);
v_val_1231_ = lean_ctor_get(v___x_1223_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v___x_1223_, 1);
v_fst_1232_ = lean_ctor_get(v_val_1231_, 0);
v_snd_1233_ = lean_ctor_get(v_val_1231_, 1);
v_isSharedCheck_1244_ = !lean_is_exclusive(v_val_1231_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1235_ = v_val_1231_;
v_isShared_1236_ = v_isSharedCheck_1244_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_snd_1233_);
lean_inc(v_fst_1232_);
lean_dec(v_val_1231_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1244_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_fst_1232_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_snd_1233_);
v___x_1238_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = lean_array_set(v_entries_1220_, v_j_1198_, v___x_1238_);
lean_dec(v_j_1198_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v___x_1239_);
v___x_1241_ = v___x_1213_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1198_);
lean_dec(v_x_1193_);
lean_dec_ref(v_inst_1190_);
return v_x_1191_;
}
}
}
else
{
lean_object* v_ks_1248_; lean_object* v_vs_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1263_; 
v_ks_1248_ = lean_ctor_get(v_x_1191_, 0);
v_vs_1249_ = lean_ctor_get(v_x_1191_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_x_1191_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1251_ = v_x_1191_;
v_isShared_1252_ = v_isSharedCheck_1263_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_vs_1249_);
lean_inc(v_ks_1248_);
lean_dec(v_x_1191_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1263_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Array_finIdxOf_x3f___redArg(v_inst_1190_, v_ks_1248_, v_x_1193_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1255_; 
if (v_isShared_1252_ == 0)
{
v___x_1255_ = v___x_1251_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_ks_1248_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_vs_1249_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
lean_object* v_val_1257_; lean_object* v_keys_x27_1258_; lean_object* v_vals_x27_1259_; lean_object* v___x_1261_; 
v_val_1257_ = lean_ctor_get(v___x_1253_, 0);
lean_inc_n(v_val_1257_, 2);
lean_dec_ref_known(v___x_1253_, 1);
v_keys_x27_1258_ = l_Array_eraseIdx___redArg(v_ks_1248_, v_val_1257_);
v_vals_x27_1259_ = l_Array_eraseIdx___redArg(v_vs_1249_, v_val_1257_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v_vals_x27_1259_);
lean_ctor_set(v___x_1251_, 0, v_keys_x27_1258_);
v___x_1261_ = v___x_1251_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_keys_x27_1258_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_vals_x27_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg___boxed(lean_object* v_inst_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_){
_start:
{
size_t v_x_202__boxed_1268_; lean_object* v_res_1269_; 
v_x_202__boxed_1268_ = lean_unbox_usize(v_x_1266_);
lean_dec(v_x_1266_);
v_res_1269_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1264_, v_x_1265_, v_x_202__boxed_1268_, v_x_1267_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux(lean_object* v_00_u03b1_1270_, lean_object* v_00_u03b2_1271_, lean_object* v_inst_1272_, lean_object* v_x_1273_, size_t v_x_1274_, lean_object* v_x_1275_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1272_, v_x_1273_, v_x_1274_, v_x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___boxed(lean_object* v_00_u03b1_1277_, lean_object* v_00_u03b2_1278_, lean_object* v_inst_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_){
_start:
{
size_t v_x_343__boxed_1283_; lean_object* v_res_1284_; 
v_x_343__boxed_1283_ = lean_unbox_usize(v_x_1281_);
lean_dec(v_x_1281_);
v_res_1284_ = l_Lean_PersistentHashMap_eraseAux(v_00_u03b1_1277_, v_00_u03b2_1278_, v_inst_1279_, v_x_1280_, v_x_343__boxed_1283_, v_x_1282_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object* v_x_1285_, lean_object* v_x_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_){
_start:
{
lean_object* v___x_1289_; uint64_t v___x_1290_; size_t v_h_1291_; lean_object* v___x_1292_; 
lean_inc(v_x_1288_);
v___x_1289_ = lean_apply_1(v_x_1286_, v_x_1288_);
v___x_1290_ = lean_unbox_uint64(v___x_1289_);
lean_dec_ref(v___x_1289_);
v_h_1291_ = lean_uint64_to_usize(v___x_1290_);
v___x_1292_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_x_1285_, v_x_1287_, v_h_1291_, v_x_1288_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase(lean_object* v_00_u03b1_1293_, lean_object* v_00_u03b2_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_, lean_object* v_x_1298_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_PersistentHashMap_erase___redArg(v_x_1295_, v_x_1296_, v_x_1297_, v_x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg(lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_f_1302_, lean_object* v_x_1303_, size_t v_x_1304_, size_t v_x_1305_, lean_object* v_x_1306_){
_start:
{
if (lean_obj_tag(v_x_1303_) == 0)
{
lean_object* v_es_1307_; size_t v___x_1308_; size_t v___x_1309_; lean_object* v_j_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_es_1307_ = lean_ctor_get(v_x_1303_, 0);
v___x_1308_ = ((size_t)31ULL);
v___x_1309_ = lean_usize_land(v_x_1304_, v___x_1308_);
v_j_1310_ = lean_usize_to_nat(v___x_1309_);
v___x_1311_ = lean_array_get_size(v_es_1307_);
v___x_1312_ = lean_nat_dec_lt(v_j_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_dec(v_j_1310_);
lean_dec(v_x_1306_);
lean_dec_ref(v_f_1302_);
lean_dec_ref(v_inst_1301_);
lean_dec_ref(v_inst_1300_);
return v_x_1303_;
}
else
{
lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1381_; 
lean_inc_ref(v_es_1307_);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_x_1303_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v_x_1303_, 0);
lean_dec(v_unused_1382_);
v___x_1314_ = v_x_1303_;
v_isShared_1315_ = v_isSharedCheck_1381_;
goto v_resetjp_1313_;
}
else
{
lean_dec(v_x_1303_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1381_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v_v_1316_; lean_object* v___x_1317_; lean_object* v_xs_x27_1318_; lean_object* v___y_1320_; 
v_v_1316_ = lean_array_fget(v_es_1307_, v_j_1310_);
v___x_1317_ = lean_box(0);
v_xs_x27_1318_ = lean_array_fset(v_es_1307_, v_j_1310_, v___x_1317_);
switch(lean_obj_tag(v_v_1316_))
{
case 0:
{
lean_object* v_key_1325_; lean_object* v_val_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
lean_dec_ref(v_inst_1301_);
v_key_1325_ = lean_ctor_get(v_v_1316_, 0);
v_val_1326_ = lean_ctor_get(v_v_1316_, 1);
lean_inc(v_key_1325_);
lean_inc(v_x_1306_);
v___x_1327_ = lean_apply_2(v_inst_1300_, v_x_1306_, v_key_1325_);
v___x_1328_ = lean_unbox(v___x_1327_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_apply_1(v_f_1302_, v___x_1329_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_dec(v_x_1306_);
v___y_1320_ = v_v_1316_;
goto v___jp_1319_;
}
else
{
lean_object* v_val_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1339_; 
lean_inc(v_val_1326_);
lean_inc(v_key_1325_);
lean_dec_ref_known(v_v_1316_, 2);
v_val_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_val_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1339_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1325_, v_val_1326_, v_x_1306_, v_val_1331_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v___x_1335_);
v___x_1337_ = v___x_1333_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
v___y_1320_ = v___x_1337_;
goto v___jp_1319_;
}
}
}
}
else
{
lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1350_; 
lean_inc(v_val_1326_);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_v_1316_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; lean_object* v_unused_1352_; 
v_unused_1351_ = lean_ctor_get(v_v_1316_, 1);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_v_1316_, 0);
lean_dec(v_unused_1352_);
v___x_1341_ = v_v_1316_;
v_isShared_1342_ = v_isSharedCheck_1350_;
goto v_resetjp_1340_;
}
else
{
lean_dec(v_v_1316_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1350_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1343_, 0, v_val_1326_);
v___x_1344_ = lean_apply_1(v_f_1302_, v___x_1343_);
if (lean_obj_tag(v___x_1344_) == 0)
{
lean_object* v___x_1345_; 
lean_del_object(v___x_1341_);
lean_dec(v_x_1306_);
v___x_1345_ = lean_box(2);
v___y_1320_ = v___x_1345_;
goto v___jp_1319_;
}
else
{
lean_object* v_val_1346_; lean_object* v___x_1348_; 
v_val_1346_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_val_1346_);
lean_dec_ref_known(v___x_1344_, 1);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 1, v_val_1346_);
lean_ctor_set(v___x_1341_, 0, v_x_1306_);
v___x_1348_ = v___x_1341_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_x_1306_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_val_1346_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
v___y_1320_ = v___x_1348_;
goto v___jp_1319_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1376_; 
v_node_1353_ = lean_ctor_get(v_v_1316_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_v_1316_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1355_ = v_v_1316_;
v_isShared_1356_ = v_isSharedCheck_1376_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_node_1353_);
lean_dec(v_v_1316_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1376_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
size_t v___x_1357_; size_t v___x_1358_; size_t v___x_1359_; size_t v___x_1360_; lean_object* v_newNode_1361_; lean_object* v___x_1362_; 
v___x_1357_ = ((size_t)5ULL);
v___x_1358_ = lean_usize_shift_right(v_x_1304_, v___x_1357_);
v___x_1359_ = ((size_t)1ULL);
v___x_1360_ = lean_usize_add(v_x_1305_, v___x_1359_);
v_newNode_1361_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1300_, v_inst_1301_, v_f_1302_, v_node_1353_, v___x_1358_, v___x_1360_, v_x_1306_);
lean_inc_ref(v_newNode_1361_);
v___x_1362_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1361_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1364_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v_newNode_1361_);
v___x_1364_ = v___x_1355_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_newNode_1361_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
v___y_1320_ = v___x_1364_;
goto v___jp_1319_;
}
}
else
{
lean_object* v_val_1366_; lean_object* v_fst_1367_; lean_object* v_snd_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v_newNode_1361_);
lean_del_object(v___x_1355_);
v_val_1366_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_val_1366_);
lean_dec_ref_known(v___x_1362_, 1);
v_fst_1367_ = lean_ctor_get(v_val_1366_, 0);
v_snd_1368_ = lean_ctor_get(v_val_1366_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_val_1366_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v_val_1366_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_snd_1368_);
lean_inc(v_fst_1367_);
lean_dec(v_val_1366_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_fst_1367_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v_snd_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
v___y_1320_ = v___x_1373_;
goto v___jp_1319_;
}
}
}
}
}
default: 
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec_ref(v_inst_1301_);
lean_dec_ref(v_inst_1300_);
v___x_1377_ = lean_box(0);
v___x_1378_ = lean_apply_1(v_f_1302_, v___x_1377_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_dec(v_x_1306_);
v___y_1320_ = v_v_1316_;
goto v___jp_1319_;
}
else
{
lean_object* v_val_1379_; lean_object* v___x_1380_; 
v_val_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_val_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v_x_1306_);
lean_ctor_set(v___x_1380_, 1, v_val_1379_);
v___y_1320_ = v___x_1380_;
goto v___jp_1319_;
}
}
}
v___jp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = lean_array_fset(v_xs_x27_1318_, v_j_1310_, v___y_1320_);
lean_dec(v_j_1310_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1321_);
v___x_1323_ = v___x_1314_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
else
{
lean_object* v_ks_1383_; lean_object* v_vs_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1417_; 
v_ks_1383_ = lean_ctor_get(v_x_1303_, 0);
v_vs_1384_ = lean_ctor_get(v_x_1303_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_x_1303_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1386_ = v_x_1303_;
v_isShared_1387_ = v_isSharedCheck_1417_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_vs_1384_);
lean_inc(v_ks_1383_);
lean_dec(v_x_1303_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1417_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; 
lean_inc(v_x_1306_);
lean_inc_ref(v_inst_1300_);
v___x_1388_ = l_Array_finIdxOf_x3f___redArg(v_inst_1300_, v_ks_1383_, v_x_1306_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v___x_1390_; 
if (v_isShared_1387_ == 0)
{
v___x_1390_ = v___x_1386_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_ks_1383_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_vs_1384_);
v___x_1390_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_apply_1(v_f_1302_, v___x_1391_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_dec(v_x_1306_);
lean_dec_ref(v_inst_1301_);
lean_dec_ref(v_inst_1300_);
return v___x_1390_;
}
else
{
lean_object* v_val_1393_; lean_object* v___x_1394_; 
v_val_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_val_1393_);
lean_dec_ref_known(v___x_1392_, 1);
v___x_1394_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_1300_, v_inst_1301_, v___x_1390_, v_x_1304_, v_x_1305_, v_x_1306_, v_val_1393_);
return v___x_1394_;
}
}
}
else
{
lean_object* v_val_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1416_; 
lean_dec_ref(v_inst_1301_);
lean_dec_ref(v_inst_1300_);
v_val_1396_ = lean_ctor_get(v___x_1388_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1398_ = v___x_1388_;
v_isShared_1399_ = v_isSharedCheck_1416_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_val_1396_);
lean_dec(v___x_1388_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1416_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v_v_x27_1400_; lean_object* v_keys_1401_; lean_object* v_vals_1402_; lean_object* v___x_1404_; 
v_v_x27_1400_ = lean_array_fget(v_vs_1384_, v_val_1396_);
lean_inc(v_val_1396_);
v_keys_1401_ = l_Array_eraseIdx___redArg(v_ks_1383_, v_val_1396_);
v_vals_1402_ = l_Array_eraseIdx___redArg(v_vs_1384_, v_val_1396_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_v_x27_1400_);
v___x_1404_ = v___x_1398_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_v_x27_1400_);
v___x_1404_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_apply_1(v_f_1302_, v___x_1404_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v___x_1407_; 
lean_dec(v_x_1306_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v_vals_1402_);
lean_ctor_set(v___x_1386_, 0, v_keys_1401_);
v___x_1407_ = v___x_1386_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_keys_1401_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_vals_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
lean_object* v_val_1409_; lean_object* v_keys_1410_; lean_object* v_vals_1411_; lean_object* v___x_1413_; 
v_val_1409_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_val_1409_);
lean_dec_ref_known(v___x_1405_, 1);
v_keys_1410_ = lean_array_push(v_keys_1401_, v_x_1306_);
v_vals_1411_ = lean_array_push(v_vals_1402_, v_val_1409_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v_vals_1411_);
lean_ctor_set(v___x_1386_, 0, v_keys_1410_);
v___x_1413_ = v___x_1386_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_keys_1410_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_vals_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg___boxed(lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_f_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
size_t v_x_413__boxed_1425_; size_t v_x_414__boxed_1426_; lean_object* v_res_1427_; 
v_x_413__boxed_1425_ = lean_unbox_usize(v_x_1422_);
lean_dec(v_x_1422_);
v_x_414__boxed_1426_ = lean_unbox_usize(v_x_1423_);
lean_dec(v_x_1423_);
v_res_1427_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1418_, v_inst_1419_, v_f_1420_, v_x_1421_, v_x_413__boxed_1425_, v_x_414__boxed_1426_, v_x_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux(lean_object* v_00_u03b1_1428_, lean_object* v_00_u03b2_1429_, lean_object* v_inst_1430_, lean_object* v_inst_1431_, lean_object* v_f_1432_, lean_object* v_x_1433_, size_t v_x_1434_, size_t v_x_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1430_, v_inst_1431_, v_f_1432_, v_x_1433_, v_x_1434_, v_x_1435_, v_x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___boxed(lean_object* v_00_u03b1_1438_, lean_object* v_00_u03b2_1439_, lean_object* v_inst_1440_, lean_object* v_inst_1441_, lean_object* v_f_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v_x_1446_){
_start:
{
size_t v_x_635__boxed_1447_; size_t v_x_636__boxed_1448_; lean_object* v_res_1449_; 
v_x_635__boxed_1447_ = lean_unbox_usize(v_x_1444_);
lean_dec(v_x_1444_);
v_x_636__boxed_1448_ = lean_unbox_usize(v_x_1445_);
lean_dec(v_x_1445_);
v_res_1449_ = l_Lean_PersistentHashMap_alterAux(v_00_u03b1_1438_, v_00_u03b2_1439_, v_inst_1440_, v_inst_1441_, v_f_1442_, v_x_1443_, v_x_635__boxed_1447_, v_x_636__boxed_1448_, v_x_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter___redArg(lean_object* v_x_1450_, lean_object* v_x_1451_, lean_object* v_x_1452_, lean_object* v_x_1453_, lean_object* v_x_1454_){
_start:
{
lean_object* v___x_1455_; uint64_t v___x_1456_; size_t v_h_1457_; size_t v___x_1458_; lean_object* v___x_1459_; 
lean_inc_ref(v_x_1451_);
lean_inc(v_x_1453_);
v___x_1455_ = lean_apply_1(v_x_1451_, v_x_1453_);
v___x_1456_ = lean_unbox_uint64(v___x_1455_);
lean_dec_ref(v___x_1455_);
v_h_1457_ = lean_uint64_to_usize(v___x_1456_);
v___x_1458_ = ((size_t)1ULL);
v___x_1459_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1450_, v_x_1451_, v_x_1454_, v_x_1452_, v_h_1457_, v___x_1458_, v_x_1453_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter(lean_object* v_00_u03b1_1460_, lean_object* v_00_u03b2_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_, lean_object* v_x_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_){
_start:
{
lean_object* v___x_1467_; uint64_t v___x_1468_; size_t v_h_1469_; size_t v___x_1470_; lean_object* v___x_1471_; 
lean_inc_ref(v_x_1463_);
lean_inc(v_x_1465_);
v___x_1467_ = lean_apply_1(v_x_1463_, v_x_1465_);
v___x_1468_ = lean_unbox_uint64(v___x_1467_);
lean_dec_ref(v___x_1467_);
v_h_1469_ = lean_uint64_to_usize(v___x_1468_);
v___x_1470_ = ((size_t)1ULL);
v___x_1471_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1462_, v_x_1463_, v_x_1466_, v_x_1464_, v_h_1469_, v___x_1470_, v_x_1465_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed(lean_object* v_i_1472_, lean_object* v_inst_1473_, lean_object* v_f_1474_, lean_object* v_keys_1475_, lean_object* v_vals_1476_, lean_object* v_____do__lift_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(v_i_1472_, v_inst_1473_, v_f_1474_, v_keys_1475_, v_vals_1476_, v_____do__lift_1477_);
lean_dec(v_i_1472_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(lean_object* v_inst_1479_, lean_object* v_f_1480_, lean_object* v_keys_1481_, lean_object* v_vals_1482_, lean_object* v_i_1483_, lean_object* v_acc_1484_){
_start:
{
lean_object* v_toApplicative_1485_; lean_object* v_toBind_1486_; lean_object* v_toPure_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v_toApplicative_1485_ = lean_ctor_get(v_inst_1479_, 0);
v_toBind_1486_ = lean_ctor_get(v_inst_1479_, 1);
lean_inc(v_toBind_1486_);
v_toPure_1487_ = lean_ctor_get(v_toApplicative_1485_, 1);
v___x_1488_ = lean_array_get_size(v_keys_1481_);
v___x_1489_ = lean_nat_dec_lt(v_i_1483_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_inc(v_toPure_1487_);
lean_dec(v_toBind_1486_);
lean_dec(v_i_1483_);
lean_dec_ref(v_vals_1482_);
lean_dec_ref(v_keys_1481_);
lean_dec(v_f_1480_);
lean_dec_ref(v_inst_1479_);
v___x_1490_ = lean_apply_2(v_toPure_1487_, lean_box(0), v_acc_1484_);
return v___x_1490_;
}
else
{
lean_object* v___f_1491_; lean_object* v_k_1492_; lean_object* v_v_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_inc_ref(v_vals_1482_);
lean_inc_ref(v_keys_1481_);
lean_inc(v_f_1480_);
lean_inc(v_i_1483_);
v___f_1491_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1491_, 0, v_i_1483_);
lean_closure_set(v___f_1491_, 1, v_inst_1479_);
lean_closure_set(v___f_1491_, 2, v_f_1480_);
lean_closure_set(v___f_1491_, 3, v_keys_1481_);
lean_closure_set(v___f_1491_, 4, v_vals_1482_);
v_k_1492_ = lean_array_fget(v_keys_1481_, v_i_1483_);
lean_dec_ref(v_keys_1481_);
v_v_1493_ = lean_array_fget(v_vals_1482_, v_i_1483_);
lean_dec(v_i_1483_);
lean_dec_ref(v_vals_1482_);
v___x_1494_ = lean_apply_3(v_f_1480_, v_acc_1484_, v_k_1492_, v_v_1493_);
v___x_1495_ = lean_apply_4(v_toBind_1486_, lean_box(0), lean_box(0), v___x_1494_, v___f_1491_);
return v___x_1495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(lean_object* v_i_1496_, lean_object* v_inst_1497_, lean_object* v_f_1498_, lean_object* v_keys_1499_, lean_object* v_vals_1500_, lean_object* v_____do__lift_1501_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_unsigned_to_nat(1u);
v___x_1503_ = lean_nat_add(v_i_1496_, v___x_1502_);
v___x_1504_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1497_, v_f_1498_, v_keys_1499_, v_vals_1500_, v___x_1503_, v_____do__lift_1501_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse(lean_object* v_m_1505_, lean_object* v_inst_1506_, lean_object* v_00_u03c3_1507_, lean_object* v_00_u03b1_1508_, lean_object* v_00_u03b2_1509_, lean_object* v_f_1510_, lean_object* v_keys_1511_, lean_object* v_vals_1512_, lean_object* v_heq_1513_, lean_object* v_i_1514_, lean_object* v_acc_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1506_, v_f_1510_, v_keys_1511_, v_vals_1512_, v_i_1514_, v_acc_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object* v_inst_1517_, lean_object* v_f_1518_, lean_object* v_x_1519_, lean_object* v_x_1520_){
_start:
{
if (lean_obj_tag(v_x_1519_) == 0)
{
lean_object* v_toApplicative_1521_; lean_object* v_toPure_1522_; lean_object* v_es_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v_toApplicative_1521_ = lean_ctor_get(v_inst_1517_, 0);
v_toPure_1522_ = lean_ctor_get(v_toApplicative_1521_, 1);
v_es_1523_ = lean_ctor_get(v_x_1519_, 0);
lean_inc_ref(v_es_1523_);
lean_dec_ref_known(v_x_1519_, 1);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = lean_array_get_size(v_es_1523_);
v___x_1526_ = lean_nat_dec_lt(v___x_1524_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; 
lean_inc(v_toPure_1522_);
lean_dec_ref(v_es_1523_);
lean_dec(v_f_1518_);
lean_dec_ref(v_inst_1517_);
v___x_1527_ = lean_apply_2(v_toPure_1522_, lean_box(0), v_x_1520_);
return v___x_1527_;
}
else
{
lean_object* v___f_1528_; uint8_t v___x_1529_; 
lean_inc(v_toPure_1522_);
lean_inc_ref(v_inst_1517_);
v___f_1528_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1528_, 0, v_f_1518_);
lean_closure_set(v___f_1528_, 1, v_inst_1517_);
lean_closure_set(v___f_1528_, 2, v_toPure_1522_);
v___x_1529_ = lean_nat_dec_le(v___x_1525_, v___x_1525_);
if (v___x_1529_ == 0)
{
if (v___x_1526_ == 0)
{
lean_object* v___x_1530_; 
lean_inc(v_toPure_1522_);
lean_dec_ref(v___f_1528_);
lean_dec_ref(v_es_1523_);
lean_dec_ref(v_inst_1517_);
v___x_1530_ = lean_apply_2(v_toPure_1522_, lean_box(0), v_x_1520_);
return v___x_1530_;
}
else
{
size_t v___x_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = ((size_t)0ULL);
v___x_1532_ = lean_usize_of_nat(v___x_1525_);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1517_, v___f_1528_, v_es_1523_, v___x_1531_, v___x_1532_, v_x_1520_);
return v___x_1533_;
}
}
else
{
size_t v___x_1534_; size_t v___x_1535_; lean_object* v___x_1536_; 
v___x_1534_ = ((size_t)0ULL);
v___x_1535_ = lean_usize_of_nat(v___x_1525_);
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1517_, v___f_1528_, v_es_1523_, v___x_1534_, v___x_1535_, v_x_1520_);
return v___x_1536_;
}
}
}
else
{
lean_object* v_ks_1537_; lean_object* v_vs_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_ks_1537_ = lean_ctor_get(v_x_1519_, 0);
lean_inc_ref(v_ks_1537_);
v_vs_1538_ = lean_ctor_get(v_x_1519_, 1);
lean_inc_ref(v_vs_1538_);
lean_dec_ref_known(v_x_1519_, 2);
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1517_, v_f_1518_, v_ks_1537_, v_vs_1538_, v___x_1539_, v_x_1520_);
return v___x_1540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0(lean_object* v_f_1541_, lean_object* v_inst_1542_, lean_object* v_toPure_1543_, lean_object* v_acc_1544_, lean_object* v_entry_1545_){
_start:
{
switch(lean_obj_tag(v_entry_1545_))
{
case 0:
{
lean_object* v_key_1546_; lean_object* v_val_1547_; lean_object* v___x_1548_; 
lean_dec(v_toPure_1543_);
lean_dec_ref(v_inst_1542_);
v_key_1546_ = lean_ctor_get(v_entry_1545_, 0);
lean_inc(v_key_1546_);
v_val_1547_ = lean_ctor_get(v_entry_1545_, 1);
lean_inc(v_val_1547_);
lean_dec_ref_known(v_entry_1545_, 2);
v___x_1548_ = lean_apply_3(v_f_1541_, v_acc_1544_, v_key_1546_, v_val_1547_);
return v___x_1548_;
}
case 1:
{
lean_object* v_node_1549_; lean_object* v___x_1550_; 
lean_dec(v_toPure_1543_);
v_node_1549_ = lean_ctor_get(v_entry_1545_, 0);
lean_inc(v_node_1549_);
lean_dec_ref_known(v_entry_1545_, 1);
v___x_1550_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1542_, v_f_1541_, v_node_1549_, v_acc_1544_);
return v___x_1550_;
}
default: 
{
lean_object* v___x_1551_; 
lean_dec_ref(v_inst_1542_);
lean_dec(v_f_1541_);
v___x_1551_ = lean_apply_2(v_toPure_1543_, lean_box(0), v_acc_1544_);
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux(lean_object* v_m_1552_, lean_object* v_inst_1553_, lean_object* v_00_u03c3_1554_, lean_object* v_00_u03b1_1555_, lean_object* v_00_u03b2_1556_, lean_object* v_f_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1553_, v_f_1557_, v_x_1558_, v_x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___redArg(lean_object* v_inst_1561_, lean_object* v_map_1562_, lean_object* v_f_1563_, lean_object* v_init_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1561_, v_f_1563_, v_map_1562_, v_init_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM(lean_object* v_m_1566_, lean_object* v_inst_1567_, lean_object* v_00_u03c3_1568_, lean_object* v_00_u03b1_1569_, lean_object* v_00_u03b2_1570_, lean_object* v_x_1571_, lean_object* v_x_1572_, lean_object* v_map_1573_, lean_object* v_f_1574_, lean_object* v_init_1575_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1567_, v_f_1574_, v_map_1573_, v_init_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___boxed(lean_object* v_m_1577_, lean_object* v_inst_1578_, lean_object* v_00_u03c3_1579_, lean_object* v_00_u03b1_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_x_1582_, lean_object* v_x_1583_, lean_object* v_map_1584_, lean_object* v_f_1585_, lean_object* v_init_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_PersistentHashMap_foldlM(v_m_1577_, v_inst_1578_, v_00_u03c3_1579_, v_00_u03b1_1580_, v_00_u03b2_1581_, v_x_1582_, v_x_1583_, v_map_1584_, v_f_1585_, v_init_1586_);
lean_dec_ref(v_x_1583_);
lean_dec_ref(v_x_1582_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg___lam__0(lean_object* v_f_1588_, lean_object* v_x_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = lean_apply_2(v_f_1588_, v___y_1590_, v___y_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg(lean_object* v_inst_1593_, lean_object* v_map_1594_, lean_object* v_f_1595_){
_start:
{
lean_object* v___f_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___f_1596_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1596_, 0, v_f_1595_);
v___x_1597_ = lean_box(0);
v___x_1598_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1593_, v___f_1596_, v_map_1594_, v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM(lean_object* v_m_1599_, lean_object* v_inst_1600_, lean_object* v_00_u03b1_1601_, lean_object* v_00_u03b2_1602_, lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v_map_1605_, lean_object* v_f_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_1600_, v_map_1605_, v_f_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___boxed(lean_object* v_m_1608_, lean_object* v_inst_1609_, lean_object* v_00_u03b1_1610_, lean_object* v_00_u03b2_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_, lean_object* v_map_1614_, lean_object* v_f_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_PersistentHashMap_forM(v_m_1608_, v_inst_1609_, v_00_u03b1_1610_, v_00_u03b2_1611_, v_x_1612_, v_x_1613_, v_map_1614_, v_f_1615_);
lean_dec_ref(v_x_1613_);
lean_dec_ref(v_x_1612_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg___lam__0(lean_object* v_f_1617_, lean_object* v_x1_1618_, lean_object* v_x2_1619_, lean_object* v_x3_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_apply_3(v_f_1617_, v_x1_1618_, v_x2_1619_, v_x3_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object* v_map_1641_, lean_object* v_f_1642_, lean_object* v_init_1643_){
_start:
{
lean_object* v___f_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___f_1644_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1644_, 0, v_f_1642_);
v___x_1645_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1646_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1645_, v___f_1644_, v_map_1641_, v_init_1643_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl(lean_object* v_00_u03c3_1647_, lean_object* v_00_u03b1_1648_, lean_object* v_00_u03b2_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_map_1652_, lean_object* v_f_1653_, lean_object* v_init_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_1652_, v_f_1653_, v_init_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___boxed(lean_object* v_00_u03c3_1656_, lean_object* v_00_u03b1_1657_, lean_object* v_00_u03b2_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_, lean_object* v_map_1661_, lean_object* v_f_1662_, lean_object* v_init_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_PersistentHashMap_foldl(v_00_u03c3_1656_, v_00_u03b1_1657_, v_00_u03b2_1658_, v_x_1659_, v_x_1660_, v_map_1661_, v_f_1662_, v_init_1663_);
lean_dec_ref(v_x_1660_);
lean_dec_ref(v_x_1659_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__0(lean_object* v_x_1665_){
_start:
{
if (lean_obj_tag(v_x_1665_) == 0)
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
v_a_1666_ = lean_ctor_get(v_x_1665_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_x_1665_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v_x_1665_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v_x_1665_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
else
{
lean_object* v_a_1674_; lean_object* v___x_1676_; uint8_t v_isShared_1677_; uint8_t v_isSharedCheck_1681_; 
v_a_1674_ = lean_ctor_get(v_x_1665_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_x_1665_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1676_ = v_x_1665_;
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
else
{
lean_inc(v_a_1674_);
lean_dec(v_x_1665_);
v___x_1676_ = lean_box(0);
v_isShared_1677_ = v_isSharedCheck_1681_;
goto v_resetjp_1675_;
}
v_resetjp_1675_:
{
lean_object* v___x_1679_; 
if (v_isShared_1677_ == 0)
{
v___x_1679_ = v___x_1676_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_a_1674_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__1(lean_object* v_toPure_1682_, lean_object* v_result_1683_){
_start:
{
lean_object* v_a_1684_; lean_object* v___x_1685_; 
v_a_1684_ = lean_ctor_get(v_result_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v_result_1683_);
v___x_1685_ = lean_apply_2(v_toPure_1682_, lean_box(0), v_a_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__2(lean_object* v_toFunctor_1686_, lean_object* v_f_1687_, lean_object* v_intoError_1688_, lean_object* v_s_1689_, lean_object* v_a_1690_, lean_object* v_b_1691_){
_start:
{
lean_object* v_map_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1701_; 
v_map_1692_ = lean_ctor_get(v_toFunctor_1686_, 0);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_toFunctor_1686_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; 
v_unused_1702_ = lean_ctor_get(v_toFunctor_1686_, 1);
lean_dec(v_unused_1702_);
v___x_1694_ = v_toFunctor_1686_;
v_isShared_1695_ = v_isSharedCheck_1701_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_map_1692_);
lean_dec(v_toFunctor_1686_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1701_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v_b_1691_);
lean_ctor_set(v___x_1694_, 0, v_a_1690_);
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_a_1690_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_b_1691_);
v___x_1697_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1698_ = lean_apply_2(v_f_1687_, v___x_1697_, v_s_1689_);
v___x_1699_ = lean_apply_4(v_map_1692_, lean_box(0), lean_box(0), v_intoError_1688_, v___x_1698_);
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg(lean_object* v_inst_1704_, lean_object* v_map_1705_, lean_object* v_init_1706_, lean_object* v_f_1707_){
_start:
{
lean_object* v_toApplicative_1708_; lean_object* v_toBind_1709_; lean_object* v___f_1710_; lean_object* v___f_1711_; lean_object* v___f_1712_; lean_object* v___f_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v_toFunctor_1720_; lean_object* v_toPure_1721_; lean_object* v_intoError_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_toApplicative_1708_ = lean_ctor_get(v_inst_1704_, 0);
lean_inc_ref(v_toApplicative_1708_);
v_toBind_1709_ = lean_ctor_get(v_inst_1704_, 1);
lean_inc(v_toBind_1709_);
lean_inc_ref_n(v_inst_1704_, 6);
v___f_1710_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1710_, 0, v_inst_1704_);
v___f_1711_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1711_, 0, v_inst_1704_);
v___f_1712_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1712_, 0, v_inst_1704_);
v___f_1713_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1713_, 0, v_inst_1704_);
v___x_1714_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1714_, 0, lean_box(0));
lean_closure_set(v___x_1714_, 1, lean_box(0));
lean_closure_set(v___x_1714_, 2, v_inst_1704_);
v___x_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
lean_ctor_set(v___x_1715_, 1, v___f_1710_);
v___x_1716_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1716_, 0, lean_box(0));
lean_closure_set(v___x_1716_, 1, lean_box(0));
lean_closure_set(v___x_1716_, 2, v_inst_1704_);
v___x_1717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
lean_ctor_set(v___x_1717_, 2, v___f_1711_);
lean_ctor_set(v___x_1717_, 3, v___f_1712_);
lean_ctor_set(v___x_1717_, 4, v___f_1713_);
v___x_1718_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1718_, 0, lean_box(0));
lean_closure_set(v___x_1718_, 1, lean_box(0));
lean_closure_set(v___x_1718_, 2, v_inst_1704_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
v_toFunctor_1720_ = lean_ctor_get(v_toApplicative_1708_, 0);
lean_inc_ref(v_toFunctor_1720_);
v_toPure_1721_ = lean_ctor_get(v_toApplicative_1708_, 1);
lean_inc(v_toPure_1721_);
lean_dec_ref(v_toApplicative_1708_);
v_intoError_1722_ = ((lean_object*)(l_Lean_PersistentHashMap_forIn___redArg___closed__0));
v___f_1723_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1723_, 0, v_toPure_1721_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__2), 6, 3);
lean_closure_set(v___f_1724_, 0, v_toFunctor_1720_);
lean_closure_set(v___f_1724_, 1, v_f_1707_);
lean_closure_set(v___f_1724_, 2, v_intoError_1722_);
lean_inc_ref(v_map_1705_);
v___x_1725_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1719_, v___f_1724_, v_map_1705_, v_init_1706_);
v___x_1726_ = lean_apply_4(v_toBind_1709_, lean_box(0), lean_box(0), v___x_1725_, v___f_1723_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___boxed(lean_object* v_inst_1727_, lean_object* v_map_1728_, lean_object* v_init_1729_, lean_object* v_f_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1727_, v_map_1728_, v_init_1729_, v_f_1730_);
lean_dec_ref(v_map_1728_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn(lean_object* v_m_1732_, lean_object* v_00_u03c3_1733_, lean_object* v_00_u03b1_1734_, lean_object* v_00_u03b2_1735_, lean_object* v_x_1736_, lean_object* v_x_1737_, lean_object* v_inst_1738_, lean_object* v_map_1739_, lean_object* v_init_1740_, lean_object* v_f_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1738_, v_map_1739_, v_init_1740_, v_f_1741_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___boxed(lean_object* v_m_1743_, lean_object* v_00_u03c3_1744_, lean_object* v_00_u03b1_1745_, lean_object* v_00_u03b2_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_, lean_object* v_inst_1749_, lean_object* v_map_1750_, lean_object* v_init_1751_, lean_object* v_f_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_PersistentHashMap_forIn(v_m_1743_, v_00_u03c3_1744_, v_00_u03b1_1745_, v_00_u03b2_1746_, v_x_1747_, v_x_1748_, v_inst_1749_, v_map_1750_, v_init_1751_, v_f_1752_);
lean_dec_ref(v_map_1750_);
lean_dec_ref(v_x_1748_);
lean_dec_ref(v_x_1747_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_inst_1754_, lean_object* v_00_u03b2_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1754_, v___y_1756_, v___y_1757_, v___y_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed(lean_object* v_inst_1760_, lean_object* v_00_u03b2_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(v_inst_1760_, v_00_u03b2_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec_ref(v___y_1762_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1766_){
_start:
{
lean_object* v___f_1767_; 
v___f_1767_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1767_, 0, v_inst_1766_);
return v___f_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad(lean_object* v_m_1768_, lean_object* v_00_u03b1_1769_, lean_object* v_00_u03b2_1770_, lean_object* v_x_1771_, lean_object* v_x_1772_, lean_object* v_inst_1773_){
_start:
{
lean_object* v___f_1774_; 
v___f_1774_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_1774_, 0, v_inst_1773_);
return v___f_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___boxed(lean_object* v_m_1775_, lean_object* v_00_u03b1_1776_, lean_object* v_00_u03b2_1777_, lean_object* v_x_1778_, lean_object* v_x_1779_, lean_object* v_inst_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_PersistentHashMap_instForInProdOfMonad(v_m_1775_, v_00_u03b1_1776_, v_00_u03b2_1777_, v_x_1778_, v_x_1779_, v_inst_1780_);
lean_dec_ref(v_x_1779_);
lean_dec_ref(v_x_1778_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__0(lean_object* v_toPure_1782_, lean_object* v_entries_x27_1783_){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v_entries_x27_1783_);
v___x_1785_ = lean_apply_2(v_toPure_1782_, lean_box(0), v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__1(lean_object* v_toPure_1786_, lean_object* v_____do__lift_1787_){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1788_, 0, v_____do__lift_1787_);
v___x_1789_ = lean_apply_2(v_toPure_1786_, lean_box(0), v___x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__2(lean_object* v_key_1790_, lean_object* v_toPure_1791_, lean_object* v_____do__lift_1792_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1793_, 0, v_key_1790_);
lean_ctor_set(v___x_1793_, 1, v_____do__lift_1792_);
v___x_1794_ = lean_apply_2(v_toPure_1791_, lean_box(0), v___x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__4(lean_object* v_ks_1795_, lean_object* v_toPure_1796_, lean_object* v_____x_1797_){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_ks_1795_);
lean_ctor_set(v___x_1798_, 1, v_____x_1797_);
v___x_1799_ = lean_apply_2(v_toPure_1796_, lean_box(0), v___x_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg(lean_object* v_inst_1800_, lean_object* v_f_1801_, lean_object* v_n_1802_){
_start:
{
if (lean_obj_tag(v_n_1802_) == 0)
{
lean_object* v_toApplicative_1803_; lean_object* v_toBind_1804_; lean_object* v_toPure_1805_; lean_object* v_es_1806_; lean_object* v___f_1807_; lean_object* v___f_1808_; lean_object* v___f_1809_; size_t v_sz_1810_; size_t v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v_toApplicative_1803_ = lean_ctor_get(v_inst_1800_, 0);
v_toBind_1804_ = lean_ctor_get(v_inst_1800_, 1);
lean_inc_n(v_toBind_1804_, 2);
v_toPure_1805_ = lean_ctor_get(v_toApplicative_1803_, 1);
v_es_1806_ = lean_ctor_get(v_n_1802_, 0);
lean_inc_ref(v_es_1806_);
lean_dec_ref_known(v_n_1802_, 1);
lean_inc_n(v_toPure_1805_, 3);
v___f_1807_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1807_, 0, v_toPure_1805_);
v___f_1808_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1808_, 0, v_toPure_1805_);
lean_inc_ref(v_inst_1800_);
v___f_1809_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1809_, 0, v_toPure_1805_);
lean_closure_set(v___f_1809_, 1, v_f_1801_);
lean_closure_set(v___f_1809_, 2, v_toBind_1804_);
lean_closure_set(v___f_1809_, 3, v_inst_1800_);
lean_closure_set(v___f_1809_, 4, v___f_1808_);
v_sz_1810_ = lean_array_size(v_es_1806_);
v___x_1811_ = ((size_t)0ULL);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1800_, v___f_1809_, v_sz_1810_, v___x_1811_, v_es_1806_);
v___x_1813_ = lean_apply_4(v_toBind_1804_, lean_box(0), lean_box(0), v___x_1812_, v___f_1807_);
return v___x_1813_;
}
else
{
lean_object* v_toApplicative_1814_; lean_object* v_toBind_1815_; lean_object* v_toPure_1816_; lean_object* v_ks_1817_; lean_object* v_vs_1818_; lean_object* v___f_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v_toApplicative_1814_ = lean_ctor_get(v_inst_1800_, 0);
v_toBind_1815_ = lean_ctor_get(v_inst_1800_, 1);
lean_inc(v_toBind_1815_);
v_toPure_1816_ = lean_ctor_get(v_toApplicative_1814_, 1);
v_ks_1817_ = lean_ctor_get(v_n_1802_, 0);
lean_inc_ref(v_ks_1817_);
v_vs_1818_ = lean_ctor_get(v_n_1802_, 1);
lean_inc_ref(v_vs_1818_);
lean_dec_ref_known(v_n_1802_, 2);
lean_inc(v_toPure_1816_);
v___f_1819_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__4), 3, 2);
lean_closure_set(v___f_1819_, 0, v_ks_1817_);
lean_closure_set(v___f_1819_, 1, v_toPure_1816_);
v___x_1820_ = l_Array_mapM_x27___redArg(v_inst_1800_, v_f_1801_, v_vs_1818_);
v___x_1821_ = lean_apply_4(v_toBind_1815_, lean_box(0), lean_box(0), v___x_1820_, v___f_1819_);
return v___x_1821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__3(lean_object* v_toPure_1822_, lean_object* v_f_1823_, lean_object* v_toBind_1824_, lean_object* v_inst_1825_, lean_object* v___f_1826_, lean_object* v_x_1827_){
_start:
{
switch(lean_obj_tag(v_x_1827_))
{
case 0:
{
lean_object* v_key_1828_; lean_object* v_val_1829_; lean_object* v___f_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v___f_1826_);
lean_dec_ref(v_inst_1825_);
v_key_1828_ = lean_ctor_get(v_x_1827_, 0);
lean_inc(v_key_1828_);
v_val_1829_ = lean_ctor_get(v_x_1827_, 1);
lean_inc(v_val_1829_);
lean_dec_ref_known(v_x_1827_, 2);
v___f_1830_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__2), 3, 2);
lean_closure_set(v___f_1830_, 0, v_key_1828_);
lean_closure_set(v___f_1830_, 1, v_toPure_1822_);
v___x_1831_ = lean_apply_1(v_f_1823_, v_val_1829_);
v___x_1832_ = lean_apply_4(v_toBind_1824_, lean_box(0), lean_box(0), v___x_1831_, v___f_1830_);
return v___x_1832_;
}
case 1:
{
lean_object* v_node_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec(v_toPure_1822_);
v_node_1833_ = lean_ctor_get(v_x_1827_, 0);
lean_inc(v_node_1833_);
lean_dec_ref_known(v_x_1827_, 1);
v___x_1834_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1825_, v_f_1823_, v_node_1833_);
v___x_1835_ = lean_apply_4(v_toBind_1824_, lean_box(0), lean_box(0), v___x_1834_, v___f_1826_);
return v___x_1835_;
}
default: 
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
lean_dec(v___f_1826_);
lean_dec_ref(v_inst_1825_);
lean_dec(v_toBind_1824_);
lean_dec(v_f_1823_);
v___x_1836_ = lean_box(2);
v___x_1837_ = lean_apply_2(v_toPure_1822_, lean_box(0), v___x_1836_);
return v___x_1837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux(lean_object* v_00_u03b1_1838_, lean_object* v_00_u03b2_1839_, lean_object* v_00_u03c3_1840_, lean_object* v_m_1841_, lean_object* v_inst_1842_, lean_object* v_f_1843_, lean_object* v_n_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1842_, v_f_1843_, v_n_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg___lam__0(lean_object* v_toPure_1846_, lean_object* v_root_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_apply_2(v_toPure_1846_, lean_box(0), v_root_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object* v_inst_1849_, lean_object* v_pm_1850_, lean_object* v_f_1851_){
_start:
{
lean_object* v_toApplicative_1852_; lean_object* v_toBind_1853_; lean_object* v_toPure_1854_; lean_object* v___x_1855_; lean_object* v___f_1856_; lean_object* v___x_1857_; 
v_toApplicative_1852_ = lean_ctor_get(v_inst_1849_, 0);
v_toBind_1853_ = lean_ctor_get(v_inst_1849_, 1);
lean_inc(v_toBind_1853_);
v_toPure_1854_ = lean_ctor_get(v_toApplicative_1852_, 1);
lean_inc(v_toPure_1854_);
v___x_1855_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_1849_, v_f_1851_, v_pm_1850_);
v___f_1856_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1856_, 0, v_toPure_1854_);
v___x_1857_ = lean_apply_4(v_toBind_1853_, lean_box(0), lean_box(0), v___x_1855_, v___f_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM(lean_object* v_00_u03b1_1858_, lean_object* v_00_u03b2_1859_, lean_object* v_00_u03c3_1860_, lean_object* v_m_1861_, lean_object* v_inst_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_, lean_object* v_pm_1865_, lean_object* v_f_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_1862_, v_pm_1865_, v_f_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___boxed(lean_object* v_00_u03b1_1868_, lean_object* v_00_u03b2_1869_, lean_object* v_00_u03c3_1870_, lean_object* v_m_1871_, lean_object* v_inst_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_, lean_object* v_pm_1875_, lean_object* v_f_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_PersistentHashMap_mapM(v_00_u03b1_1868_, v_00_u03b2_1869_, v_00_u03c3_1870_, v_m_1871_, v_inst_1872_, v_x_1873_, v_x_1874_, v_pm_1875_, v_f_1876_);
lean_dec_ref(v_x_1874_);
lean_dec_ref(v_x_1873_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg___lam__0(lean_object* v_f_1878_, lean_object* v_x_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_apply_1(v_f_1878_, v_x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg(lean_object* v_pm_1881_, lean_object* v_f_1882_){
_start:
{
lean_object* v___f_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___f_1883_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1883_, 0, v_f_1882_);
v___x_1884_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1885_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_1884_, v_pm_1881_, v___f_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map(lean_object* v_00_u03b1_1886_, lean_object* v_00_u03b2_1887_, lean_object* v_00_u03c3_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_pm_1891_, lean_object* v_f_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_PersistentHashMap_map___redArg(v_pm_1891_, v_f_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___boxed(lean_object* v_00_u03b1_1894_, lean_object* v_00_u03b2_1895_, lean_object* v_00_u03c3_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v_pm_1899_, lean_object* v_f_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_PersistentHashMap_map(v_00_u03b1_1894_, v_00_u03b2_1895_, v_00_u03c3_1896_, v_x_1897_, v_x_1898_, v_pm_1899_, v_f_1900_);
lean_dec_ref(v_x_1898_);
lean_dec_ref(v_x_1897_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg___lam__0(lean_object* v_ps_1902_, lean_object* v_k_1903_, lean_object* v_v_1904_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_k_1903_);
lean_ctor_set(v___x_1905_, 1, v_v_1904_);
v___x_1906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v_ps_1902_);
return v___x_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg(lean_object* v_m_1908_){
_start:
{
lean_object* v___f_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___f_1909_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___redArg___closed__0));
v___x_1910_ = lean_box(0);
v___x_1911_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1908_, v___f_1909_, v___x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList(lean_object* v_00_u03b1_1912_, lean_object* v_00_u03b2_1913_, lean_object* v_x_1914_, lean_object* v_x_1915_, lean_object* v_m_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_PersistentHashMap_toList___redArg(v_m_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___boxed(lean_object* v_00_u03b1_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v_m_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_PersistentHashMap_toList(v_00_u03b1_1918_, v_00_u03b2_1919_, v_x_1920_, v_x_1921_, v_m_1922_);
lean_dec_ref(v_x_1921_);
lean_dec_ref(v_x_1920_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg___lam__0(lean_object* v_ps_1924_, lean_object* v_k_1925_, lean_object* v_v_1926_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v_k_1925_);
lean_ctor_set(v___x_1927_, 1, v_v_1926_);
v___x_1928_ = lean_array_push(v_ps_1924_, v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg(lean_object* v_m_1932_){
_start:
{
lean_object* v___f_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___f_1933_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__0));
v___x_1934_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__1));
v___x_1935_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_1932_, v___f_1933_, v___x_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray(lean_object* v_00_u03b1_1936_, lean_object* v_00_u03b2_1937_, lean_object* v_x_1938_, lean_object* v_x_1939_, lean_object* v_m_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Lean_PersistentHashMap_toArray___redArg(v_m_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___boxed(lean_object* v_00_u03b1_1942_, lean_object* v_00_u03b2_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v_m_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_PersistentHashMap_toArray(v_00_u03b1_1942_, v_00_u03b2_1943_, v_x_1944_, v_x_1945_, v_m_1946_);
lean_dec_ref(v_x_1945_);
lean_dec_ref(v_x_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg(lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_){
_start:
{
if (lean_obj_tag(v_x_1948_) == 0)
{
lean_object* v_es_1951_; lean_object* v_numNodes_1952_; lean_object* v_numNull_1953_; lean_object* v_numCollisions_1954_; lean_object* v_maxDepth_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1977_; 
v_es_1951_ = lean_ctor_get(v_x_1948_, 0);
v_numNodes_1952_ = lean_ctor_get(v_x_1949_, 0);
v_numNull_1953_ = lean_ctor_get(v_x_1949_, 1);
v_numCollisions_1954_ = lean_ctor_get(v_x_1949_, 2);
v_maxDepth_1955_ = lean_ctor_get(v_x_1949_, 3);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_x_1949_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1957_ = v_x_1949_;
v_isShared_1958_ = v_isSharedCheck_1977_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_maxDepth_1955_);
lean_inc(v_numCollisions_1954_);
lean_inc(v_numNull_1953_);
lean_inc(v_numNodes_1952_);
lean_dec(v_x_1949_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1977_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___y_1962_; uint8_t v___x_1976_; 
v___x_1959_ = lean_unsigned_to_nat(1u);
v___x_1960_ = lean_nat_add(v_numNodes_1952_, v___x_1959_);
lean_dec(v_numNodes_1952_);
v___x_1976_ = lean_nat_dec_le(v_maxDepth_1955_, v_x_1950_);
if (v___x_1976_ == 0)
{
v___y_1962_ = v_maxDepth_1955_;
goto v___jp_1961_;
}
else
{
lean_dec(v_maxDepth_1955_);
lean_inc(v_x_1950_);
v___y_1962_ = v_x_1950_;
goto v___jp_1961_;
}
v___jp_1961_:
{
lean_object* v_stats_1964_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 3, v___y_1962_);
lean_ctor_set(v___x_1957_, 0, v___x_1960_);
v_stats_1964_ = v___x_1957_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_numNull_1953_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_numCollisions_1954_);
lean_ctor_set(v_reuseFailAlloc_1975_, 3, v___y_1962_);
v_stats_1964_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; uint8_t v___x_1967_; 
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_array_get_size(v_es_1951_);
v___x_1967_ = lean_nat_dec_lt(v___x_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_dec(v_x_1950_);
return v_stats_1964_;
}
else
{
uint8_t v___x_1968_; 
v___x_1968_ = lean_nat_dec_le(v___x_1966_, v___x_1966_);
if (v___x_1968_ == 0)
{
if (v___x_1967_ == 0)
{
lean_dec(v_x_1950_);
return v_stats_1964_;
}
else
{
size_t v___x_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((size_t)0ULL);
v___x_1970_ = lean_usize_of_nat(v___x_1966_);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1950_, v_es_1951_, v___x_1969_, v___x_1970_, v_stats_1964_);
lean_dec(v_x_1950_);
return v___x_1971_;
}
}
else
{
size_t v___x_1972_; size_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = ((size_t)0ULL);
v___x_1973_ = lean_usize_of_nat(v___x_1966_);
v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_1950_, v_es_1951_, v___x_1972_, v___x_1973_, v_stats_1964_);
lean_dec(v_x_1950_);
return v___x_1974_;
}
}
}
}
}
}
else
{
lean_object* v_ks_1978_; lean_object* v_numNodes_1979_; lean_object* v_numNull_1980_; lean_object* v_numCollisions_1981_; lean_object* v_maxDepth_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1998_; 
v_ks_1978_ = lean_ctor_get(v_x_1948_, 0);
v_numNodes_1979_ = lean_ctor_get(v_x_1949_, 0);
v_numNull_1980_ = lean_ctor_get(v_x_1949_, 1);
v_numCollisions_1981_ = lean_ctor_get(v_x_1949_, 2);
v_maxDepth_1982_ = lean_ctor_get(v_x_1949_, 3);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_x_1949_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1984_ = v_x_1949_;
v_isShared_1985_ = v_isSharedCheck_1998_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_maxDepth_1982_);
lean_inc(v_numCollisions_1981_);
lean_inc(v_numNull_1980_);
lean_inc(v_numNodes_1979_);
lean_dec(v_x_1949_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1998_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1986_ = lean_unsigned_to_nat(1u);
v___x_1987_ = lean_nat_add(v_numNodes_1979_, v___x_1986_);
lean_dec(v_numNodes_1979_);
v___x_1988_ = lean_array_get_size(v_ks_1978_);
v___x_1989_ = lean_nat_add(v_numCollisions_1981_, v___x_1988_);
lean_dec(v_numCollisions_1981_);
v___x_1990_ = lean_nat_sub(v___x_1989_, v___x_1986_);
lean_dec(v___x_1989_);
v___x_1991_ = lean_nat_dec_le(v_maxDepth_1982_, v_x_1950_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1993_; 
lean_dec(v_x_1950_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 2, v___x_1990_);
lean_ctor_set(v___x_1984_, 0, v___x_1987_);
v___x_1993_ = v___x_1984_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_numNull_1980_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_maxDepth_1982_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
else
{
lean_object* v___x_1996_; 
lean_dec(v_maxDepth_1982_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 3, v_x_1950_);
lean_ctor_set(v___x_1984_, 2, v___x_1990_);
lean_ctor_set(v___x_1984_, 0, v___x_1987_);
v___x_1996_ = v___x_1984_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_numNull_1980_);
lean_ctor_set(v_reuseFailAlloc_1997_, 2, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_1997_, 3, v_x_1950_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(lean_object* v_x_1999_, lean_object* v_as_2000_, size_t v_i_2001_, size_t v_stop_2002_, lean_object* v_b_2003_){
_start:
{
lean_object* v___y_2005_; uint8_t v___x_2009_; 
v___x_2009_ = lean_usize_dec_eq(v_i_2001_, v_stop_2002_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = lean_array_uget_borrowed(v_as_2000_, v_i_2001_);
switch(lean_obj_tag(v___x_2011_))
{
case 0:
{
v___y_2005_ = v_b_2003_;
goto v___jp_2004_;
}
case 1:
{
lean_object* v_node_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_node_2012_ = lean_ctor_get(v___x_2011_, 0);
v___x_2013_ = lean_nat_add(v_x_1999_, v___x_2010_);
v___x_2014_ = l_Lean_PersistentHashMap_collectStats___redArg(v_node_2012_, v_b_2003_, v___x_2013_);
v___y_2005_ = v___x_2014_;
goto v___jp_2004_;
}
default: 
{
lean_object* v_numNodes_2015_; lean_object* v_numNull_2016_; lean_object* v_numCollisions_2017_; lean_object* v_maxDepth_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2026_; 
v_numNodes_2015_ = lean_ctor_get(v_b_2003_, 0);
v_numNull_2016_ = lean_ctor_get(v_b_2003_, 1);
v_numCollisions_2017_ = lean_ctor_get(v_b_2003_, 2);
v_maxDepth_2018_ = lean_ctor_get(v_b_2003_, 3);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_b_2003_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2020_ = v_b_2003_;
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_maxDepth_2018_);
lean_inc(v_numCollisions_2017_);
lean_inc(v_numNull_2016_);
lean_inc(v_numNodes_2015_);
lean_dec(v_b_2003_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2026_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = lean_nat_add(v_numNull_2016_, v___x_2010_);
lean_dec(v_numNull_2016_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 1, v___x_2022_);
v___x_2024_ = v___x_2020_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_numNodes_2015_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_numCollisions_2017_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_maxDepth_2018_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
v___y_2005_ = v___x_2024_;
goto v___jp_2004_;
}
}
}
}
}
else
{
return v_b_2003_;
}
v___jp_2004_:
{
size_t v___x_2006_; size_t v___x_2007_; 
v___x_2006_ = ((size_t)1ULL);
v___x_2007_ = lean_usize_add(v_i_2001_, v___x_2006_);
v_i_2001_ = v___x_2007_;
v_b_2003_ = v___y_2005_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg___boxed(lean_object* v_x_2027_, lean_object* v_as_2028_, lean_object* v_i_2029_, lean_object* v_stop_2030_, lean_object* v_b_2031_){
_start:
{
size_t v_i_boxed_2032_; size_t v_stop_boxed_2033_; lean_object* v_res_2034_; 
v_i_boxed_2032_ = lean_unbox_usize(v_i_2029_);
lean_dec(v_i_2029_);
v_stop_boxed_2033_ = lean_unbox_usize(v_stop_2030_);
lean_dec(v_stop_2030_);
v_res_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2027_, v_as_2028_, v_i_boxed_2032_, v_stop_boxed_2033_, v_b_2031_);
lean_dec_ref(v_as_2028_);
lean_dec(v_x_2027_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg___boxed(lean_object* v_x_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2035_, v_x_2036_, v_x_2037_);
lean_dec_ref(v_x_2035_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats(lean_object* v_00_u03b1_2039_, lean_object* v_00_u03b2_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2041_, v_x_2042_, v_x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___boxed(lean_object* v_00_u03b1_2045_, lean_object* v_00_u03b2_2046_, lean_object* v_x_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lean_PersistentHashMap_collectStats(v_00_u03b1_2045_, v_00_u03b2_2046_, v_x_2047_, v_x_2048_, v_x_2049_);
lean_dec_ref(v_x_2047_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(lean_object* v_00_u03b1_2051_, lean_object* v_00_u03b2_2052_, lean_object* v_x_2053_, lean_object* v_as_2054_, size_t v_i_2055_, size_t v_stop_2056_, lean_object* v_b_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2053_, v_as_2054_, v_i_2055_, v_stop_2056_, v_b_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2059_, lean_object* v_00_u03b2_2060_, lean_object* v_x_2061_, lean_object* v_as_2062_, lean_object* v_i_2063_, lean_object* v_stop_2064_, lean_object* v_b_2065_){
_start:
{
size_t v_i_boxed_2066_; size_t v_stop_boxed_2067_; lean_object* v_res_2068_; 
v_i_boxed_2066_ = lean_unbox_usize(v_i_2063_);
lean_dec(v_i_2063_);
v_stop_boxed_2067_ = lean_unbox_usize(v_stop_2064_);
lean_dec(v_stop_2064_);
v_res_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(v_00_u03b1_2059_, v_00_u03b2_2060_, v_x_2061_, v_as_2062_, v_i_boxed_2066_, v_stop_boxed_2067_, v_b_2065_);
lean_dec_ref(v_as_2062_);
lean_dec(v_x_2061_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg(lean_object* v_m_2071_){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = ((lean_object*)(l_Lean_PersistentHashMap_stats___redArg___closed__0));
v___x_2073_ = lean_unsigned_to_nat(1u);
v___x_2074_ = l_Lean_PersistentHashMap_collectStats___redArg(v_m_2071_, v___x_2072_, v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg___boxed(lean_object* v_m_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2075_);
lean_dec_ref(v_m_2075_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats(lean_object* v_00_u03b1_2077_, lean_object* v_00_u03b2_2078_, lean_object* v_x_2079_, lean_object* v_x_2080_, lean_object* v_m_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___boxed(lean_object* v_00_u03b1_2083_, lean_object* v_00_u03b2_2084_, lean_object* v_x_2085_, lean_object* v_x_2086_, lean_object* v_m_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_PersistentHashMap_stats(v_00_u03b1_2083_, v_00_u03b2_2084_, v_x_2085_, v_x_2086_, v_m_2087_);
lean_dec_ref(v_m_2087_);
lean_dec_ref(v_x_2086_);
lean_dec_ref(v_x_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Stats_toString(lean_object* v_s_2094_){
_start:
{
lean_object* v_numNodes_2095_; lean_object* v_numNull_2096_; lean_object* v_numCollisions_2097_; lean_object* v_maxDepth_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_numNodes_2095_ = lean_ctor_get(v_s_2094_, 0);
lean_inc(v_numNodes_2095_);
v_numNull_2096_ = lean_ctor_get(v_s_2094_, 1);
lean_inc(v_numNull_2096_);
v_numCollisions_2097_ = lean_ctor_get(v_s_2094_, 2);
lean_inc(v_numCollisions_2097_);
v_maxDepth_2098_ = lean_ctor_get(v_s_2094_, 3);
lean_inc(v_maxDepth_2098_);
lean_dec_ref(v_s_2094_);
v___x_2099_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__0));
v___x_2100_ = l_Nat_reprFast(v_numNodes_2095_);
v___x_2101_ = lean_string_append(v___x_2099_, v___x_2100_);
lean_dec_ref(v___x_2100_);
v___x_2102_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__1));
v___x_2103_ = lean_string_append(v___x_2101_, v___x_2102_);
v___x_2104_ = l_Nat_reprFast(v_numNull_2096_);
v___x_2105_ = lean_string_append(v___x_2103_, v___x_2104_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__2));
v___x_2107_ = lean_string_append(v___x_2105_, v___x_2106_);
v___x_2108_ = l_Nat_reprFast(v_numCollisions_2097_);
v___x_2109_ = lean_string_append(v___x_2107_, v___x_2108_);
lean_dec_ref(v___x_2108_);
v___x_2110_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__3));
v___x_2111_ = lean_string_append(v___x_2109_, v___x_2110_);
v___x_2112_ = l_Nat_reprFast(v_maxDepth_2098_);
v___x_2113_ = lean_string_append(v___x_2111_, v___x_2112_);
lean_dec_ref(v___x_2112_);
v___x_2114_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__4));
v___x_2115_ = lean_string_append(v___x_2113_, v___x_2114_);
return v___x_2115_;
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
