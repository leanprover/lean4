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
size_t lean_ptr_addr(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_finIdxOf_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___impl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_PersistentHashMap_Entry_ctorIdx___impl___redArg(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_00_u03b2_6_, lean_object* v_00_u03c3_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_tag_nat(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorIdx___impl___boxed(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_00_u03c3_12_, lean_object* v_x_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_PersistentHashMap_Entry_ctorIdx___impl(v_00_u03b1_10_, v_00_u03b2_11_, v_00_u03c3_12_, v_x_13_);
lean_dec(v_x_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorElim___redArg(lean_object* v_t_15_, lean_object* v_k_16_){
_start:
{
switch(lean_obj_tag(v_t_15_))
{
case 0:
{
lean_object* v_key_17_; lean_object* v_val_18_; lean_object* v___x_19_; 
v_key_17_ = lean_ctor_get(v_t_15_, 0);
lean_inc(v_key_17_);
v_val_18_ = lean_ctor_get(v_t_15_, 1);
lean_inc(v_val_18_);
lean_dec_ref_known(v_t_15_, 2);
v___x_19_ = lean_apply_2(v_k_16_, v_key_17_, v_val_18_);
return v___x_19_;
}
case 1:
{
lean_object* v_node_20_; lean_object* v___x_21_; 
v_node_20_ = lean_ctor_get(v_t_15_, 0);
lean_inc(v_node_20_);
lean_dec_ref_known(v_t_15_, 1);
v___x_21_ = lean_apply_1(v_k_16_, v_node_20_);
return v___x_21_;
}
default: 
{
return v_k_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorElim(lean_object* v_00_u03b1_22_, lean_object* v_00_u03b2_23_, lean_object* v_00_u03c3_24_, lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_27_, v_k_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ctorElim___boxed(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_00_u03c3_33_, lean_object* v_motive_34_, lean_object* v_ctorIdx_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_k_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_PersistentHashMap_Entry_ctorElim(v_00_u03b1_31_, v_00_u03b2_32_, v_00_u03c3_33_, v_motive_34_, v_ctorIdx_35_, v_t_36_, v_h_37_, v_k_38_);
lean_dec(v_ctorIdx_35_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_entry_elim___redArg(lean_object* v_t_40_, lean_object* v_entry_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_40_, v_entry_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_entry_elim(lean_object* v_00_u03b1_43_, lean_object* v_00_u03b2_44_, lean_object* v_00_u03c3_45_, lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_entry_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_47_, v_entry_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ref_elim___redArg(lean_object* v_t_51_, lean_object* v_ref_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_51_, v_ref_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_ref_elim(lean_object* v_00_u03b1_54_, lean_object* v_00_u03b2_55_, lean_object* v_00_u03c3_56_, lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_ref_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_58_, v_ref_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_null_elim___redArg(lean_object* v_t_62_, lean_object* v_null_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_62_, v_null_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Entry_null_elim(lean_object* v_00_u03b1_65_, lean_object* v_00_u03b2_66_, lean_object* v_00_u03c3_67_, lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_null_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_PersistentHashMap_Entry_ctorElim___redArg(v_t_69_, v_null_71_);
return v___x_72_;
}
}
lean_object* l_Lean_PersistentHashMap_instInhabitedEntry___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(2);
return v___x_74_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_instInhabitedEntry___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_75_;
v_res_75_ = l_Lean_PersistentHashMap_instInhabitedEntry___redArg();
stack->m_obj
 = v_res_75_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry___redArg___boxed(lean_object* v___dummy_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_PersistentHashMap_instInhabitedEntry___redArg();
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object* v_00_u03b1_78_, lean_object* v_00_u03b2_79_, lean_object* v_00_u03c3_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_box(2);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl___redArg(lean_object* v_x_82_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_obj_tag_nat(v_x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl___redArg___boxed(lean_object* v_x_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_PersistentHashMap_Node_ctorIdx___impl___redArg(v_x_84_);
lean_dec_ref(v_x_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl(lean_object* v_00_u03b1_86_, lean_object* v_00_u03b2_87_, lean_object* v_x_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_tag_nat(v_x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl___boxed(lean_object* v_00_u03b1_90_, lean_object* v_00_u03b2_91_, lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_PersistentHashMap_Node_ctorIdx___impl(v_00_u03b1_90_, v_00_u03b2_91_, v_x_92_);
lean_dec_ref(v_x_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim___redArg(lean_object* v_t_94_, lean_object* v_k_95_){
_start:
{
if (lean_obj_tag(v_t_94_) == 0)
{
lean_object* v_es_96_; lean_object* v___x_97_; 
v_es_96_ = lean_ctor_get(v_t_94_, 0);
lean_inc_ref(v_es_96_);
lean_dec_ref_known(v_t_94_, 1);
v___x_97_ = lean_apply_1(v_k_95_, v_es_96_);
return v___x_97_;
}
else
{
lean_object* v_ks_98_; lean_object* v_vs_99_; lean_object* v___x_100_; 
v_ks_98_ = lean_ctor_get(v_t_94_, 0);
lean_inc_ref(v_ks_98_);
v_vs_99_ = lean_ctor_get(v_t_94_, 1);
lean_inc_ref(v_vs_99_);
lean_dec_ref_known(v_t_94_, 2);
v___x_100_ = lean_apply_3(v_k_95_, v_ks_98_, v_vs_99_, lean_box(0));
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_motive__1_103_, lean_object* v_ctorIdx_104_, lean_object* v_t_105_, lean_object* v_h_106_, lean_object* v_k_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_105_, v_k_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim___boxed(lean_object* v_00_u03b1_109_, lean_object* v_00_u03b2_110_, lean_object* v_motive__1_111_, lean_object* v_ctorIdx_112_, lean_object* v_t_113_, lean_object* v_h_114_, lean_object* v_k_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_PersistentHashMap_Node_ctorElim(v_00_u03b1_109_, v_00_u03b2_110_, v_motive__1_111_, v_ctorIdx_112_, v_t_113_, v_h_114_, v_k_115_);
lean_dec(v_ctorIdx_112_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_entries_elim___redArg(lean_object* v_t_117_, lean_object* v_entries_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_117_, v_entries_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_entries_elim(lean_object* v_00_u03b1_120_, lean_object* v_00_u03b2_121_, lean_object* v_motive__1_122_, lean_object* v_t_123_, lean_object* v_h_124_, lean_object* v_entries_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_123_, v_entries_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_collision_elim___redArg(lean_object* v_t_127_, lean_object* v_collision_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_127_, v_collision_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_collision_elim(lean_object* v_00_u03b1_130_, lean_object* v_00_u03b2_131_, lean_object* v_motive__1_132_, lean_object* v_t_133_, lean_object* v_h_134_, lean_object* v_collision_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_133_, v_collision_135_);
return v___x_136_;
}
}
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v_es_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_es_138_ = lean_ctor_get(v_x_137_, 0);
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = lean_array_get_size(v_es_138_);
v___x_141_ = lean_nat_dec_lt(v___x_139_, v___x_140_);
if (v___x_141_ == 0)
{
uint8_t v___x_142_; 
v___x_142_ = 1;
return v___x_142_;
}
else
{
if (v___x_141_ == 0)
{
return v___x_141_;
}
else
{
size_t v___x_143_; size_t v___x_144_; uint8_t v___x_145_; 
v___x_143_ = ((size_t)0ULL);
v___x_144_ = lean_usize_of_nat(v___x_140_);
v___x_145_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_es_138_, v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
return v___x_141_;
}
else
{
uint8_t v___x_146_; 
v___x_146_ = 0;
return v___x_146_;
}
}
}
}
else
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_Node_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_137_ = stack[0].m_obj;
uint8_t v_res_148_;
v_res_148_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_137_);
stack->m_num = v_res_148_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(lean_object* v_as_149_, size_t v_i_150_, size_t v_stop_151_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = lean_usize_dec_eq(v_i_150_, v_stop_151_);
if (v___x_156_ == 0)
{
uint8_t v___x_157_; lean_object* v___x_158_; 
v___x_157_ = 1;
v___x_158_ = lean_array_uget_borrowed(v_as_149_, v_i_150_);
switch(lean_obj_tag(v___x_158_))
{
case 0:
{
return v___x_157_;
}
case 1:
{
lean_object* v_node_159_; uint8_t v___x_160_; 
v_node_159_ = lean_ctor_get(v___x_158_, 0);
v___x_160_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_node_159_);
if (v___x_160_ == 0)
{
return v___x_157_;
}
else
{
goto v___jp_152_;
}
}
default: 
{
goto v___jp_152_;
}
}
}
else
{
uint8_t v___x_161_; 
v___x_161_ = 0;
return v___x_161_;
}
v___jp_152_:
{
size_t v___x_153_; size_t v___x_154_; 
v___x_153_ = ((size_t)1ULL);
v___x_154_ = lean_usize_add(v_i_150_, v___x_153_);
v_i_150_ = v___x_154_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_149_ = stack[0].m_obj;
size_t v_i_150_ = stack[1].m_num;
size_t v_stop_151_ = stack[2].m_num;
uint8_t v_res_162_;
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_as_149_, v_i_150_, v_stop_151_);
stack->m_num = v_res_162_;
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
uint8_t l_Lean_PersistentHashMap_Node_isEmpty(lean_object* v_00_u03b1_173_, lean_object* v_00_u03b2_174_, lean_object* v_x_175_){
_start:
{
uint8_t v___x_176_; 
v___x_176_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_175_);
return v___x_176_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_Node_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_175_ = stack[2].m_obj;
uint8_t v_res_177_;
v_res_177_ = l_Lean_PersistentHashMap_Node_isEmpty(lean_box(0), lean_box(0), v_x_175_);
stack->m_num = v_res_177_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_isEmpty___boxed(lean_object* v_00_u03b1_178_, lean_object* v_00_u03b2_179_, lean_object* v_x_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Lean_PersistentHashMap_Node_isEmpty(v_00_u03b1_178_, v_00_u03b2_179_, v_x_180_);
lean_dec_ref(v_x_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_as_185_, size_t v_i_186_, size_t v_stop_187_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_as_185_, v_i_186_, v_stop_187_);
return v___x_188_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_185_ = stack[2].m_obj;
size_t v_i_186_ = stack[3].m_num;
size_t v_stop_187_ = stack[4].m_num;
uint8_t v_res_189_;
v_res_189_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(lean_box(0), lean_box(0), v_as_185_, v_i_186_, v_stop_187_);
stack->m_num = v_res_189_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___boxed(lean_object* v_00_u03b1_190_, lean_object* v_00_u03b2_191_, lean_object* v_as_192_, lean_object* v_i_193_, lean_object* v_stop_194_){
_start:
{
size_t v_i_boxed_195_; size_t v_stop_boxed_196_; uint8_t v_res_197_; lean_object* v_r_198_; 
v_i_boxed_195_ = lean_unbox_usize(v_i_193_);
lean_dec(v_i_193_);
v_stop_boxed_196_ = lean_unbox_usize(v_stop_194_);
lean_dec(v_stop_194_);
v_res_197_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0(v_00_u03b1_190_, v_00_u03b2_191_, v_as_192_, v_i_boxed_195_, v_stop_boxed_196_);
lean_dec_ref(v_as_192_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
lean_object* l_Lean_PersistentHashMap_instInhabitedNode___redArg(){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = ((lean_object*)(l_Lean_PersistentHashMap_instInhabitedNode___redArg___closed__1));
return v___x_204_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_instInhabitedNode___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_205_;
v_res_205_ = l_Lean_PersistentHashMap_instInhabitedNode___redArg();
stack->m_obj
 = v_res_205_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode___redArg___boxed(lean_object* v___dummy_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_PersistentHashMap_instInhabitedNode___redArg();
return v_res_207_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_instInhabitedNode___closed__0(void){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Lean_PersistentHashMap_instInhabitedNode___redArg();
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = lean_obj_once(&l_Lean_PersistentHashMap_instInhabitedNode___closed__0, &l_Lean_PersistentHashMap_instInhabitedNode___closed__0_once, _init_l_Lean_PersistentHashMap_instInhabitedNode___closed__0);
return v___x_211_;
}
}
static size_t _init_l_Lean_PersistentHashMap_shift(void){
_start:
{
size_t v___x_212_; 
v___x_212_ = ((size_t)5ULL);
return v___x_212_;
}
}
static size_t _init_l_Lean_PersistentHashMap_branching(void){
_start:
{
size_t v___x_213_; 
v___x_213_ = ((size_t)32ULL);
return v___x_213_;
}
}
static size_t _init_l_Lean_PersistentHashMap_maxDepth(void){
_start:
{
size_t v___x_214_; 
v___x_214_ = ((size_t)7ULL);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_maxCollisions(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_unsigned_to_nat(4u);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_box(2);
v___x_217_ = lean_unsigned_to_nat(32u);
v___x_218_ = lean_mk_array(v___x_217_, v___x_216_);
return v___x_218_;
}
}
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg(){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0);
return v___x_220_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_221_;
v_res_221_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___boxed(lean_object* v___dummy_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v_res_223_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0(void){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object* v_00_u03b1_225_, lean_object* v_00_u03b2_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0);
return v___x_227_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_228_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0);
v___x_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
return v___x_229_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___redArg(){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___redArg___closed__0, &l_Lean_PersistentHashMap_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___redArg___closed__0);
return v___x_231_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_232_;
v_res_232_ = l_Lean_PersistentHashMap_empty___redArg();
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___redArg___boxed(lean_object* v___dummy_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_PersistentHashMap_empty___redArg();
return v_res_234_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___closed__0(void){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty(lean_object* v_00_u03b1_236_, lean_object* v_00_u03b2_237_, lean_object* v_inst_238_, lean_object* v_inst_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___closed__0, &l_Lean_PersistentHashMap_empty___closed__0_once, _init_l_Lean_PersistentHashMap_empty___closed__0);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___boxed(lean_object* v_00_u03b1_241_, lean_object* v_00_u03b2_242_, lean_object* v_inst_243_, lean_object* v_inst_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_PersistentHashMap_empty(v_00_u03b1_241_, v_00_u03b2_242_, v_inst_243_, v_inst_244_);
lean_dec_ref(v_inst_244_);
lean_dec_ref(v_inst_243_);
return v_res_245_;
}
}
uint8_t l_Lean_PersistentHashMap_isEmpty___redArg(lean_object* v_x_246_){
_start:
{
uint8_t v___x_247_; 
v___x_247_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_246_);
return v___x_247_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_246_ = stack[0].m_obj;
uint8_t v_res_248_;
v_res_248_ = l_Lean_PersistentHashMap_isEmpty___redArg(v_x_246_);
stack->m_num = v_res_248_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___redArg___boxed(lean_object* v_x_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Lean_PersistentHashMap_isEmpty___redArg(v_x_249_);
lean_dec_ref(v_x_249_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
uint8_t l_Lean_PersistentHashMap_isEmpty(lean_object* v_00_u03b1_252_, lean_object* v_00_u03b2_253_, lean_object* v_x_254_, lean_object* v_x_255_, lean_object* v_x_256_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_256_);
return v___x_257_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_254_ = stack[2].m_obj;
lean_object* v_x_255_ = stack[3].m_obj;
lean_object* v_x_256_ = stack[4].m_obj;
uint8_t v_res_258_;
v_res_258_ = l_Lean_PersistentHashMap_isEmpty(lean_box(0), lean_box(0), v_x_254_, v_x_255_, v_x_256_);
stack->m_num = v_res_258_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___boxed(lean_object* v_00_u03b1_259_, lean_object* v_00_u03b2_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = l_Lean_PersistentHashMap_isEmpty(v_00_u03b1_259_, v_00_u03b2_260_, v_x_261_, v_x_262_, v_x_263_);
lean_dec_ref(v_x_263_);
lean_dec_ref(v_x_262_);
lean_dec_ref(v_x_261_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
lean_object* l_Lean_PersistentHashMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___redArg___closed__0, &l_Lean_PersistentHashMap_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___redArg___closed__0);
return v___x_267_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_268_;
v_res_268_ = l_Lean_PersistentHashMap_instInhabited___redArg();
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___redArg___boxed(lean_object* v___dummy_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v_res_270_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object* v_00_u03b1_272_, lean_object* v_00_u03b2_273_, lean_object* v_inst_274_, lean_object* v_inst_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = lean_obj_once(&l_Lean_PersistentHashMap_instInhabited___closed__0, &l_Lean_PersistentHashMap_instInhabited___closed__0_once, _init_l_Lean_PersistentHashMap_instInhabited___closed__0);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___boxed(lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_inst_279_, lean_object* v_inst_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_PersistentHashMap_instInhabited(v_00_u03b1_277_, v_00_u03b2_278_, v_inst_279_, v_inst_280_);
lean_dec_ref(v_inst_280_);
lean_dec_ref(v_inst_279_);
return v_res_281_;
}
}
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg(){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___redArg___closed__0, &l_Lean_PersistentHashMap_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___redArg___closed__0);
return v___x_283_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_mkEmptyEntries___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_284_;
v_res_284_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
stack->m_obj
 = v_res_284_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg___boxed(lean_object* v___dummy_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v_res_286_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_mkEmptyEntries___closed__0(void){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntries___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntries___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntries___closed__0);
return v___x_290_;
}
}
size_t l_Lean_PersistentHashMap_mul2Shift(size_t v_i_291_, size_t v_shift_292_){
_start:
{
size_t v___x_293_; 
v___x_293_ = lean_usize_shift_left(v_i_291_, v_shift_292_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_mul2Shift_0interp(lean_interpreter_value* stack)
{
size_t v_i_291_ = stack[0].m_num;
size_t v_shift_292_ = stack[1].m_num;
size_t v_res_294_;
v_res_294_ = l_Lean_PersistentHashMap_mul2Shift(v_i_291_, v_shift_292_);
stack->m_num = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mul2Shift___boxed(lean_object* v_i_295_, lean_object* v_shift_296_){
_start:
{
size_t v_i_boxed_297_; size_t v_shift_boxed_298_; size_t v_res_299_; lean_object* v_r_300_; 
v_i_boxed_297_ = lean_unbox_usize(v_i_295_);
lean_dec(v_i_295_);
v_shift_boxed_298_ = lean_unbox_usize(v_shift_296_);
lean_dec(v_shift_296_);
v_res_299_ = l_Lean_PersistentHashMap_mul2Shift(v_i_boxed_297_, v_shift_boxed_298_);
v_r_300_ = lean_box_usize(v_res_299_);
return v_r_300_;
}
}
size_t l_Lean_PersistentHashMap_div2Shift(size_t v_i_301_, size_t v_shift_302_){
_start:
{
size_t v___x_303_; 
v___x_303_ = lean_usize_shift_right(v_i_301_, v_shift_302_);
return v___x_303_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_div2Shift_0interp(lean_interpreter_value* stack)
{
size_t v_i_301_ = stack[0].m_num;
size_t v_shift_302_ = stack[1].m_num;
size_t v_res_304_;
v_res_304_ = l_Lean_PersistentHashMap_div2Shift(v_i_301_, v_shift_302_);
stack->m_num = v_res_304_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_div2Shift___boxed(lean_object* v_i_305_, lean_object* v_shift_306_){
_start:
{
size_t v_i_boxed_307_; size_t v_shift_boxed_308_; size_t v_res_309_; lean_object* v_r_310_; 
v_i_boxed_307_ = lean_unbox_usize(v_i_305_);
lean_dec(v_i_305_);
v_shift_boxed_308_ = lean_unbox_usize(v_shift_306_);
lean_dec(v_shift_306_);
v_res_309_ = l_Lean_PersistentHashMap_div2Shift(v_i_boxed_307_, v_shift_boxed_308_);
v_r_310_ = lean_box_usize(v_res_309_);
return v_r_310_;
}
}
size_t l_Lean_PersistentHashMap_mod2Shift(size_t v_i_311_, size_t v_shift_312_){
_start:
{
size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v___x_316_; 
v___x_313_ = ((size_t)1ULL);
v___x_314_ = lean_usize_shift_left(v___x_313_, v_shift_312_);
v___x_315_ = lean_usize_sub(v___x_314_, v___x_313_);
v___x_316_ = lean_usize_land(v_i_311_, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_mod2Shift_0interp(lean_interpreter_value* stack)
{
size_t v_i_311_ = stack[0].m_num;
size_t v_shift_312_ = stack[1].m_num;
size_t v_res_317_;
v_res_317_ = l_Lean_PersistentHashMap_mod2Shift(v_i_311_, v_shift_312_);
stack->m_num = v_res_317_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mod2Shift___boxed(lean_object* v_i_318_, lean_object* v_shift_319_){
_start:
{
size_t v_i_boxed_320_; size_t v_shift_boxed_321_; size_t v_res_322_; lean_object* v_r_323_; 
v_i_boxed_320_ = lean_unbox_usize(v_i_318_);
lean_dec(v_i_318_);
v_shift_boxed_321_ = lean_unbox_usize(v_shift_319_);
lean_dec(v_shift_319_);
v_res_322_ = l_Lean_PersistentHashMap_mod2Shift(v_i_boxed_320_, v_shift_boxed_321_);
v_r_323_ = lean_box_usize(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(lean_object* v_inst_324_, lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_ks_329_; lean_object* v_vs_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_355_; 
v_ks_329_ = lean_ctor_get(v_x_325_, 0);
v_vs_330_ = lean_ctor_get(v_x_325_, 1);
v_isSharedCheck_355_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_355_ == 0)
{
v___x_332_ = v_x_325_;
v_isShared_333_ = v_isSharedCheck_355_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_vs_330_);
lean_inc(v_ks_329_);
lean_dec(v_x_325_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_355_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_array_get_size(v_ks_329_);
v___x_335_ = lean_nat_dec_lt(v_x_326_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
lean_dec(v_x_326_);
lean_dec_ref(v_inst_324_);
v___x_336_ = lean_array_push(v_ks_329_, v_x_327_);
v___x_337_ = lean_array_push(v_vs_330_, v_x_328_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_337_);
lean_ctor_set(v___x_332_, 0, v___x_336_);
v___x_339_ = v___x_332_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
else
{
lean_object* v_k_x27_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v_k_x27_341_ = lean_array_fget_borrowed(v_ks_329_, v_x_326_);
lean_inc_ref(v_inst_324_);
lean_inc(v_k_x27_341_);
lean_inc(v_x_327_);
v___x_342_ = lean_apply_2(v_inst_324_, v_x_327_, v_k_x27_341_);
v___x_343_ = lean_unbox(v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_345_; 
if (v_isShared_333_ == 0)
{
v___x_345_ = v___x_332_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_ks_329_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_vs_330_);
v___x_345_ = v_reuseFailAlloc_349_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_x_326_, v___x_346_);
lean_dec(v_x_326_);
v_x_325_ = v___x_345_;
v_x_326_ = v___x_347_;
goto _start;
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
lean_dec_ref(v_inst_324_);
v___x_350_ = lean_array_fset(v_ks_329_, v_x_326_, v_x_327_);
v___x_351_ = lean_array_fset(v_vs_330_, v_x_326_, v_x_328_);
lean_dec(v_x_326_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_351_);
lean_ctor_set(v___x_332_, 0, v___x_350_);
v___x_353_ = v___x_332_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_350_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux(lean_object* v_00_u03b1_356_, lean_object* v_00_u03b2_357_, lean_object* v_inst_358_, lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(v_inst_358_, v_x_359_, v_x_360_, v_x_361_, v_x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(lean_object* v_inst_364_, lean_object* v_n_365_, lean_object* v_k_366_, lean_object* v_v_367_){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(v_inst_364_, v_n_365_, v___x_368_, v_k_366_, v_v_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode(lean_object* v_00_u03b1_370_, lean_object* v_00_u03b2_371_, lean_object* v_inst_372_, lean_object* v_n_373_, lean_object* v_k_374_, lean_object* v_v_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(v_inst_372_, v_n_373_, v_k_374_, v_v_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object* v_x_377_){
_start:
{
lean_object* v_ks_378_; lean_object* v___x_379_; 
v_ks_378_ = lean_ctor_get(v_x_377_, 0);
v___x_379_ = lean_array_get_size(v_ks_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg___boxed(lean_object* v_x_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_380_);
lean_dec_ref(v_x_380_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize(lean_object* v_00_u03b1_382_, lean_object* v_00_u03b2_383_, lean_object* v_x_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___boxed(lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_x_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_PersistentHashMap_getCollisionNodeSize(v_00_u03b1_386_, v_00_u03b2_387_, v_x_388_);
lean_dec_ref(v_x_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object* v_k_u2081_390_, lean_object* v_v_u2081_391_, lean_object* v_k_u2082_392_, lean_object* v_v_u2082_393_){
_start:
{
lean_object* v___x_394_; lean_object* v_ks_395_; lean_object* v___x_396_; lean_object* v_ks_397_; lean_object* v___x_398_; lean_object* v_vs_399_; lean_object* v___x_400_; 
v___x_394_ = lean_unsigned_to_nat(4u);
v_ks_395_ = lean_mk_empty_array_with_capacity(v___x_394_);
lean_inc_ref(v_ks_395_);
v___x_396_ = lean_array_push(v_ks_395_, v_k_u2081_390_);
v_ks_397_ = lean_array_push(v___x_396_, v_k_u2082_392_);
v___x_398_ = lean_array_push(v_ks_395_, v_v_u2081_391_);
v_vs_399_ = lean_array_push(v___x_398_, v_v_u2082_393_);
v___x_400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_400_, 0, v_ks_397_);
lean_ctor_set(v___x_400_, 1, v_vs_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode(lean_object* v_00_u03b1_401_, lean_object* v_00_u03b2_402_, lean_object* v_k_u2081_403_, lean_object* v_v_u2081_404_, lean_object* v_k_u2082_405_, lean_object* v_v_u2082_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_k_u2081_403_, v_v_u2081_404_, v_k_u2082_405_, v_v_u2082_406_);
return v___x_407_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___redArg(lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_x_410_, size_t v_x_411_, size_t v_x_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_410_) == 0)
{
lean_object* v_es_415_; size_t v___x_416_; size_t v___x_417_; lean_object* v_j_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_es_415_ = lean_ctor_get(v_x_410_, 0);
v___x_416_ = ((size_t)31ULL);
v___x_417_ = lean_usize_land(v_x_411_, v___x_416_);
v_j_418_ = lean_usize_to_nat(v___x_417_);
v___x_419_ = lean_array_get_size(v_es_415_);
v___x_420_ = lean_nat_dec_lt(v_j_418_, v___x_419_);
if (v___x_420_ == 0)
{
lean_dec(v_j_418_);
lean_dec(v_x_414_);
lean_dec(v_x_413_);
lean_dec_ref(v_inst_409_);
lean_dec_ref(v_inst_408_);
return v_x_410_;
}
else
{
lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_460_; 
lean_inc_ref(v_es_415_);
v_isSharedCheck_460_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v_x_410_, 0);
lean_dec(v_unused_461_);
v___x_422_ = v_x_410_;
v_isShared_423_ = v_isSharedCheck_460_;
goto v_resetjp_421_;
}
else
{
lean_dec(v_x_410_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_460_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_v_424_; lean_object* v___x_425_; lean_object* v_xs_x27_426_; lean_object* v___y_428_; 
v_v_424_ = lean_array_fget(v_es_415_, v_j_418_);
v___x_425_ = lean_box(0);
v_xs_x27_426_ = lean_array_fset(v_es_415_, v_j_418_, v___x_425_);
switch(lean_obj_tag(v_v_424_))
{
case 0:
{
lean_object* v_key_433_; lean_object* v_val_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_445_; 
lean_dec_ref(v_inst_409_);
v_key_433_ = lean_ctor_get(v_v_424_, 0);
v_val_434_ = lean_ctor_get(v_v_424_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_v_424_);
if (v_isSharedCheck_445_ == 0)
{
v___x_436_ = v_v_424_;
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_val_434_);
lean_inc(v_key_433_);
lean_dec(v_v_424_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_445_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; uint8_t v___x_439_; 
lean_inc(v_key_433_);
lean_inc(v_x_413_);
v___x_438_ = lean_apply_2(v_inst_408_, v_x_413_, v_key_433_);
v___x_439_ = lean_unbox(v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; lean_object* v___x_441_; 
lean_del_object(v___x_436_);
v___x_440_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_433_, v_val_434_, v_x_413_, v_x_414_);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
v___y_428_ = v___x_441_;
goto v___jp_427_;
}
else
{
lean_object* v___x_443_; 
lean_dec(v_val_434_);
lean_dec(v_key_433_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v_x_414_);
lean_ctor_set(v___x_436_, 0, v_x_413_);
v___x_443_ = v___x_436_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_x_413_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_x_414_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
v___y_428_ = v___x_443_;
goto v___jp_427_;
}
}
}
}
case 1:
{
lean_object* v_node_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_458_; 
v_node_446_ = lean_ctor_get(v_v_424_, 0);
v_isSharedCheck_458_ = !lean_is_exclusive(v_v_424_);
if (v_isSharedCheck_458_ == 0)
{
v___x_448_ = v_v_424_;
v_isShared_449_ = v_isSharedCheck_458_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_node_446_);
lean_dec(v_v_424_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_458_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
size_t v___x_450_; size_t v___x_451_; size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_456_; 
v___x_450_ = ((size_t)5ULL);
v___x_451_ = lean_usize_shift_right(v_x_411_, v___x_450_);
v___x_452_ = ((size_t)1ULL);
v___x_453_ = lean_usize_add(v_x_412_, v___x_452_);
v___x_454_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_408_, v_inst_409_, v_node_446_, v___x_451_, v___x_453_, v_x_413_, v_x_414_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_454_);
v___x_456_ = v___x_448_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
v___y_428_ = v___x_456_;
goto v___jp_427_;
}
}
}
default: 
{
lean_object* v___x_459_; 
lean_dec_ref(v_inst_409_);
lean_dec_ref(v_inst_408_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_x_413_);
lean_ctor_set(v___x_459_, 1, v_x_414_);
v___y_428_ = v___x_459_;
goto v___jp_427_;
}
}
v___jp_427_:
{
lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_429_ = lean_array_fset(v_xs_x27_426_, v_j_418_, v___y_428_);
lean_dec(v_j_418_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_429_);
v___x_431_ = v___x_422_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
else
{
lean_object* v_ks_462_; lean_object* v_vs_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_481_; 
v_ks_462_ = lean_ctor_get(v_x_410_, 0);
v_vs_463_ = lean_ctor_get(v_x_410_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_410_);
if (v_isSharedCheck_481_ == 0)
{
v___x_465_ = v_x_410_;
v_isShared_466_ = v_isSharedCheck_481_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_vs_463_);
lean_inc(v_ks_462_);
lean_dec(v_x_410_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_481_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_ks_462_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_vs_463_);
v___x_468_ = v_reuseFailAlloc_480_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v_val_469_; size_t v___x_470_; uint8_t v___x_471_; 
lean_inc_ref(v_inst_408_);
v_val_469_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(v_inst_408_, v___x_468_, v_x_413_, v_x_414_);
v___x_470_ = ((size_t)7ULL);
v___x_471_ = lean_usize_dec_le(v___x_470_, v_x_412_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_472_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_val_469_);
v___x_473_ = lean_unsigned_to_nat(4u);
v___x_474_ = lean_nat_dec_lt(v___x_472_, v___x_473_);
lean_dec(v___x_472_);
if (v___x_474_ == 0)
{
lean_object* v_ks_475_; lean_object* v_vs_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_ks_475_ = lean_ctor_get(v_val_469_, 0);
lean_inc_ref(v_ks_475_);
v_vs_476_ = lean_ctor_get(v_val_469_, 1);
lean_inc_ref(v_vs_476_);
lean_dec_ref(v_val_469_);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntries___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntries___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntries___closed__0);
v___x_479_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_408_, v_inst_409_, v_x_412_, v_ks_475_, v_vs_476_, v___x_477_, v___x_478_);
lean_dec_ref(v_vs_476_);
lean_dec_ref(v_ks_475_);
return v___x_479_;
}
else
{
lean_dec_ref(v_inst_409_);
lean_dec_ref(v_inst_408_);
return v_val_469_;
}
}
else
{
lean_dec_ref(v_inst_409_);
lean_dec_ref(v_inst_408_);
return v_val_469_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_408_ = stack[0].m_obj;
lean_object* v_inst_409_ = stack[1].m_obj;
lean_object* v_x_410_ = stack[2].m_obj;
size_t v_x_411_ = stack[3].m_num;
size_t v_x_412_ = stack[4].m_num;
lean_object* v_x_413_ = stack[5].m_obj;
lean_object* v_x_414_ = stack[6].m_obj;
lean_object* v_res_482_;
v_res_482_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_408_, v_inst_409_, v_x_410_, v_x_411_, v_x_412_, v_x_413_, v_x_414_);
stack->m_obj
 = v_res_482_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(lean_object* v_inst_483_, lean_object* v_inst_484_, size_t v_depth_485_, lean_object* v_keys_486_, lean_object* v_vals_487_, lean_object* v_i_488_, lean_object* v_entries_489_){
_start:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_array_get_size(v_keys_486_);
v___x_491_ = lean_nat_dec_lt(v_i_488_, v___x_490_);
if (v___x_491_ == 0)
{
lean_dec(v_i_488_);
lean_dec_ref(v_inst_484_);
lean_dec_ref(v_inst_483_);
return v_entries_489_;
}
else
{
lean_object* v_k_492_; lean_object* v_v_493_; lean_object* v___x_494_; uint64_t v___x_495_; size_t v_h_496_; size_t v___x_497_; lean_object* v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v_h_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v_k_492_ = lean_array_fget_borrowed(v_keys_486_, v_i_488_);
v_v_493_ = lean_array_fget_borrowed(v_vals_487_, v_i_488_);
lean_inc_ref_n(v_inst_484_, 2);
lean_inc_n(v_k_492_, 2);
v___x_494_ = lean_apply_1(v_inst_484_, v_k_492_);
v___x_495_ = lean_unbox_uint64(v___x_494_);
lean_dec_ref(v___x_494_);
v_h_496_ = lean_uint64_to_usize(v___x_495_);
v___x_497_ = ((size_t)5ULL);
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_sub(v_depth_485_, v___x_499_);
v___x_501_ = lean_usize_mul(v___x_497_, v___x_500_);
v_h_502_ = lean_usize_shift_right(v_h_496_, v___x_501_);
v___x_503_ = lean_nat_add(v_i_488_, v___x_498_);
lean_dec(v_i_488_);
lean_inc(v_v_493_);
lean_inc_ref(v_inst_483_);
v___x_504_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_483_, v_inst_484_, v_entries_489_, v_h_502_, v_depth_485_, v_k_492_, v_v_493_);
v_i_488_ = v___x_503_;
v_entries_489_ = v___x_504_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_483_ = stack[0].m_obj;
lean_object* v_inst_484_ = stack[1].m_obj;
size_t v_depth_485_ = stack[2].m_num;
lean_object* v_keys_486_ = stack[3].m_obj;
lean_object* v_vals_487_ = stack[4].m_obj;
lean_object* v_i_488_ = stack[5].m_obj;
lean_object* v_entries_489_ = stack[6].m_obj;
lean_object* v_res_506_;
v_res_506_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_483_, v_inst_484_, v_depth_485_, v_keys_486_, v_vals_487_, v_i_488_, v_entries_489_);
stack->m_obj
 = v_res_506_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg___boxed(lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_depth_509_, lean_object* v_keys_510_, lean_object* v_vals_511_, lean_object* v_i_512_, lean_object* v_entries_513_){
_start:
{
size_t v_depth_boxed_514_; lean_object* v_res_515_; 
v_depth_boxed_514_ = lean_unbox_usize(v_depth_509_);
lean_dec(v_depth_509_);
v_res_515_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_507_, v_inst_508_, v_depth_boxed_514_, v_keys_510_, v_vals_511_, v_i_512_, v_entries_513_);
lean_dec_ref(v_vals_511_);
lean_dec_ref(v_keys_510_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg___boxed(lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
size_t v_x_394__boxed_523_; size_t v_x_395__boxed_524_; lean_object* v_res_525_; 
v_x_394__boxed_523_ = lean_unbox_usize(v_x_519_);
lean_dec(v_x_519_);
v_x_395__boxed_524_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_res_525_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_516_, v_inst_517_, v_x_518_, v_x_394__boxed_523_, v_x_395__boxed_524_, v_x_521_, v_x_522_);
return v_res_525_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b2_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, size_t v_depth_530_, lean_object* v_keys_531_, lean_object* v_vals_532_, lean_object* v_heq_533_, lean_object* v_i_534_, lean_object* v_entries_535_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_528_, v_inst_529_, v_depth_530_, v_keys_531_, v_vals_532_, v_i_534_, v_entries_535_);
return v___x_536_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_528_ = stack[2].m_obj;
lean_object* v_inst_529_ = stack[3].m_obj;
size_t v_depth_530_ = stack[4].m_num;
lean_object* v_keys_531_ = stack[5].m_obj;
lean_object* v_vals_532_ = stack[6].m_obj;
lean_object* v_i_534_ = stack[8].m_obj;
lean_object* v_entries_535_ = stack[9].m_obj;
lean_object* v_res_537_;
v_res_537_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(lean_box(0), lean_box(0), v_inst_528_, v_inst_529_, v_depth_530_, v_keys_531_, v_vals_532_, lean_box(0), v_i_534_, v_entries_535_);
stack->m_obj
 = v_res_537_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___boxed(lean_object* v_00_u03b1_538_, lean_object* v_00_u03b2_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_depth_542_, lean_object* v_keys_543_, lean_object* v_vals_544_, lean_object* v_heq_545_, lean_object* v_i_546_, lean_object* v_entries_547_){
_start:
{
size_t v_depth_boxed_548_; lean_object* v_res_549_; 
v_depth_boxed_548_ = lean_unbox_usize(v_depth_542_);
lean_dec(v_depth_542_);
v_res_549_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(v_00_u03b1_538_, v_00_u03b2_539_, v_inst_540_, v_inst_541_, v_depth_boxed_548_, v_keys_543_, v_vals_544_, v_heq_545_, v_i_546_, v_entries_547_);
lean_dec_ref(v_vals_544_);
lean_dec_ref(v_keys_543_);
return v_res_549_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux(lean_object* v_00_u03b1_550_, lean_object* v_00_u03b2_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_x_554_, size_t v_x_555_, size_t v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_552_, v_inst_553_, v_x_554_, v_x_555_, v_x_556_, v_x_557_, v_x_558_);
return v___x_559_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_552_ = stack[2].m_obj;
lean_object* v_inst_553_ = stack[3].m_obj;
lean_object* v_x_554_ = stack[4].m_obj;
size_t v_x_555_ = stack[5].m_num;
size_t v_x_556_ = stack[6].m_num;
lean_object* v_x_557_ = stack[7].m_obj;
lean_object* v_x_558_ = stack[8].m_obj;
lean_object* v_res_560_;
v_res_560_ = l_Lean_PersistentHashMap_insertAux(lean_box(0), lean_box(0), v_inst_552_, v_inst_553_, v_x_554_, v_x_555_, v_x_556_, v_x_557_, v_x_558_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___boxed(lean_object* v_00_u03b1_561_, lean_object* v_00_u03b2_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_x_565_, lean_object* v_x_566_, lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
size_t v_x_668__boxed_570_; size_t v_x_669__boxed_571_; lean_object* v_res_572_; 
v_x_668__boxed_570_ = lean_unbox_usize(v_x_566_);
lean_dec(v_x_566_);
v_x_669__boxed_571_ = lean_unbox_usize(v_x_567_);
lean_dec(v_x_567_);
v_res_572_ = l_Lean_PersistentHashMap_insertAux(v_00_u03b1_561_, v_00_u03b2_562_, v_inst_563_, v_inst_564_, v_x_565_, v_x_668__boxed_570_, v_x_669__boxed_571_, v_x_568_, v_x_569_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object* v_x_573_, lean_object* v_x_574_, lean_object* v_x_575_, lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
lean_object* v___x_578_; uint64_t v___x_579_; size_t v___x_580_; size_t v___x_581_; lean_object* v___x_582_; 
lean_inc_ref(v_x_574_);
lean_inc(v_x_576_);
v___x_578_ = lean_apply_1(v_x_574_, v_x_576_);
v___x_579_ = lean_unbox_uint64(v___x_578_);
lean_dec_ref(v___x_578_);
v___x_580_ = lean_uint64_to_usize(v___x_579_);
v___x_581_ = ((size_t)1ULL);
v___x_582_ = l_Lean_PersistentHashMap_insertAux___redArg(v_x_573_, v_x_574_, v_x_575_, v___x_580_, v___x_581_, v_x_576_, v_x_577_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert(lean_object* v_00_u03b1_583_, lean_object* v_00_u03b2_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_PersistentHashMap_insert___redArg(v_x_585_, v_x_586_, v_x_587_, v_x_588_, v_x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg(lean_object* v_inst_591_, lean_object* v_keys_592_, lean_object* v_vals_593_, lean_object* v_i_594_, lean_object* v_k_595_){
_start:
{
lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_596_ = lean_array_get_size(v_keys_592_);
v___x_597_ = lean_nat_dec_lt(v_i_594_, v___x_596_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; 
lean_dec(v_k_595_);
lean_dec(v_i_594_);
lean_dec_ref(v_inst_591_);
v___x_598_ = lean_box(0);
return v___x_598_;
}
else
{
lean_object* v_k_x27_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_k_x27_599_ = lean_array_fget_borrowed(v_keys_592_, v_i_594_);
lean_inc_ref(v_inst_591_);
lean_inc(v_k_x27_599_);
lean_inc(v_k_595_);
v___x_600_ = lean_apply_2(v_inst_591_, v_k_595_, v_k_x27_599_);
v___x_601_ = lean_unbox(v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_add(v_i_594_, v___x_602_);
lean_dec(v_i_594_);
v_i_594_ = v___x_603_;
goto _start;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_k_595_);
lean_dec_ref(v_inst_591_);
v___x_605_ = lean_array_fget_borrowed(v_vals_593_, v_i_594_);
lean_dec(v_i_594_);
lean_inc(v___x_605_);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
return v___x_606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg___boxed(lean_object* v_inst_607_, lean_object* v_keys_608_, lean_object* v_vals_609_, lean_object* v_i_610_, lean_object* v_k_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_607_, v_keys_608_, v_vals_609_, v_i_610_, v_k_611_);
lean_dec_ref(v_vals_609_);
lean_dec_ref(v_keys_608_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux(lean_object* v_00_u03b1_613_, lean_object* v_00_u03b2_614_, lean_object* v_inst_615_, lean_object* v_keys_616_, lean_object* v_vals_617_, lean_object* v_heq_618_, lean_object* v_i_619_, lean_object* v_k_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_615_, v_keys_616_, v_vals_617_, v_i_619_, v_k_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___boxed(lean_object* v_00_u03b1_622_, lean_object* v_00_u03b2_623_, lean_object* v_inst_624_, lean_object* v_keys_625_, lean_object* v_vals_626_, lean_object* v_heq_627_, lean_object* v_i_628_, lean_object* v_k_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_PersistentHashMap_findAtAux(v_00_u03b1_622_, v_00_u03b2_623_, v_inst_624_, v_keys_625_, v_vals_626_, v_heq_627_, v_i_628_, v_k_629_);
lean_dec_ref(v_vals_626_);
lean_dec_ref(v_keys_625_);
return v_res_630_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___redArg(lean_object* v_inst_631_, lean_object* v_x_632_, size_t v_x_633_, lean_object* v_x_634_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_object* v_es_635_; lean_object* v___x_636_; size_t v___x_637_; size_t v___x_638_; lean_object* v_j_639_; lean_object* v___x_640_; 
v_es_635_ = lean_ctor_get(v_x_632_, 0);
lean_inc_ref(v_es_635_);
lean_dec_ref_known(v_x_632_, 1);
v___x_636_ = lean_box(2);
v___x_637_ = ((size_t)31ULL);
v___x_638_ = lean_usize_land(v_x_633_, v___x_637_);
v_j_639_ = lean_usize_to_nat(v___x_638_);
v___x_640_ = lean_array_get(v___x_636_, v_es_635_, v_j_639_);
lean_dec(v_j_639_);
lean_dec_ref(v_es_635_);
switch(lean_obj_tag(v___x_640_))
{
case 0:
{
lean_object* v_key_641_; lean_object* v_val_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_key_641_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_key_641_);
v_val_642_ = lean_ctor_get(v___x_640_, 1);
lean_inc(v_val_642_);
lean_dec_ref_known(v___x_640_, 2);
v___x_643_ = lean_apply_2(v_inst_631_, v_x_634_, v_key_641_);
v___x_644_ = lean_unbox(v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec(v_val_642_);
v___x_645_ = lean_box(0);
return v___x_645_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v_val_642_);
return v___x_646_;
}
}
case 1:
{
lean_object* v_node_647_; size_t v___x_648_; size_t v___x_649_; 
v_node_647_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_node_647_);
lean_dec_ref_known(v___x_640_, 1);
v___x_648_ = ((size_t)5ULL);
v___x_649_ = lean_usize_shift_right(v_x_633_, v___x_648_);
v_x_632_ = v_node_647_;
v_x_633_ = v___x_649_;
goto _start;
}
default: 
{
lean_object* v___x_651_; 
lean_dec(v_x_634_);
lean_dec_ref(v_inst_631_);
v___x_651_ = lean_box(0);
return v___x_651_;
}
}
}
else
{
lean_object* v_ks_652_; lean_object* v_vs_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_ks_652_ = lean_ctor_get(v_x_632_, 0);
lean_inc_ref(v_ks_652_);
v_vs_653_ = lean_ctor_get(v_x_632_, 1);
lean_inc_ref(v_vs_653_);
lean_dec_ref_known(v_x_632_, 2);
v___x_654_ = lean_unsigned_to_nat(0u);
v___x_655_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_631_, v_ks_652_, v_vs_653_, v___x_654_, v_x_634_);
lean_dec_ref(v_vs_653_);
lean_dec_ref(v_ks_652_);
return v___x_655_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_631_ = stack[0].m_obj;
lean_object* v_x_632_ = stack[1].m_obj;
size_t v_x_633_ = stack[2].m_num;
lean_object* v_x_634_ = stack[3].m_obj;
lean_object* v_res_656_;
v_res_656_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_631_, v_x_632_, v_x_633_, v_x_634_);
stack->m_obj
 = v_res_656_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg___boxed(lean_object* v_inst_657_, lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
size_t v_x_118__boxed_661_; lean_object* v_res_662_; 
v_x_118__boxed_661_ = lean_unbox_usize(v_x_659_);
lean_dec(v_x_659_);
v_res_662_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_657_, v_x_658_, v_x_118__boxed_661_, v_x_660_);
return v_res_662_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux(lean_object* v_00_u03b1_663_, lean_object* v_00_u03b2_664_, lean_object* v_inst_665_, lean_object* v_x_666_, size_t v_x_667_, lean_object* v_x_668_){
_start:
{
lean_object* v___x_669_; 
lean_inc_ref(v_x_666_);
v___x_669_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_665_, v_x_666_, v_x_667_, v_x_668_);
return v___x_669_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_665_ = stack[2].m_obj;
lean_object* v_x_666_ = stack[3].m_obj;
size_t v_x_667_ = stack[4].m_num;
lean_object* v_x_668_ = stack[5].m_obj;
lean_object* v_res_670_;
v_res_670_ = l_Lean_PersistentHashMap_findAux(lean_box(0), lean_box(0), v_inst_665_, v_x_666_, v_x_667_, v_x_668_);
stack->m_obj
 = v_res_670_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___boxed(lean_object* v_00_u03b1_671_, lean_object* v_00_u03b2_672_, lean_object* v_inst_673_, lean_object* v_x_674_, lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
size_t v_x_198__boxed_677_; lean_object* v_res_678_; 
v_x_198__boxed_677_ = lean_unbox_usize(v_x_675_);
lean_dec(v_x_675_);
v_res_678_ = l_Lean_PersistentHashMap_findAux(v_00_u03b1_671_, v_00_u03b2_672_, v_inst_673_, v_x_674_, v_x_198__boxed_677_, v_x_676_);
lean_dec_ref(v_x_674_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
lean_object* v___x_683_; uint64_t v___x_684_; size_t v___x_685_; lean_object* v___x_686_; 
lean_inc(v_x_682_);
v___x_683_ = lean_apply_1(v_x_680_, v_x_682_);
v___x_684_ = lean_unbox_uint64(v___x_683_);
lean_dec_ref(v___x_683_);
v___x_685_ = lean_uint64_to_usize(v___x_684_);
lean_inc_ref(v_x_681_);
v___x_686_ = l_Lean_PersistentHashMap_findAux___redArg(v_x_679_, v_x_681_, v___x_685_, v_x_682_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg___boxed(lean_object* v_x_687_, lean_object* v_x_688_, lean_object* v_x_689_, lean_object* v_x_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_687_, v_x_688_, v_x_689_, v_x_690_);
lean_dec_ref(v_x_689_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f(lean_object* v_00_u03b1_692_, lean_object* v_00_u03b2_693_, lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_694_, v_x_695_, v_x_696_, v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___boxed(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_PersistentHashMap_find_x3f(v_00_u03b1_699_, v_00_u03b2_700_, v_x_701_, v_x_702_, v_x_703_, v_x_704_);
lean_dec_ref(v_x_703_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(lean_object* v_x_706_, lean_object* v_x_707_, lean_object* v_m_708_, lean_object* v_i_709_, lean_object* v_x_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_706_, v_x_707_, v_m_708_, v_i_709_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed(lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v_m_714_, lean_object* v_i_715_, lean_object* v_x_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(v_x_712_, v_x_713_, v_m_714_, v_i_715_, v_x_716_);
lean_dec_ref(v_m_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg(lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
lean_object* v___f_720_; 
v___f_720_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_720_, 0, v_x_718_);
lean_closure_set(v___f_720_, 1, v_x_719_);
return v___f_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue(lean_object* v_00_u03b1_721_, lean_object* v_00_u03b2_722_, lean_object* v_x_723_, lean_object* v_x_724_){
_start:
{
lean_object* v___f_725_; 
v___f_725_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_725_, 0, v_x_723_);
lean_closure_set(v___f_725_, 1, v_x_724_);
return v___f_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg(lean_object* v_x_726_, lean_object* v_x_727_, lean_object* v_m_728_, lean_object* v_a_729_, lean_object* v_b_u2080_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_726_, v_x_727_, v_m_728_, v_a_729_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_inc(v_b_u2080_730_);
return v_b_u2080_730_;
}
else
{
lean_object* v_val_732_; 
v_val_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_val_732_);
lean_dec_ref_known(v___x_731_, 1);
return v_val_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg___boxed(lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_m_735_, lean_object* v_a_736_, lean_object* v_b_u2080_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_PersistentHashMap_findD___redArg(v_x_733_, v_x_734_, v_m_735_, v_a_736_, v_b_u2080_737_);
lean_dec(v_b_u2080_737_);
lean_dec_ref(v_m_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD(lean_object* v_00_u03b1_739_, lean_object* v_00_u03b2_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_m_743_, lean_object* v_a_744_, lean_object* v_b_u2080_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_741_, v_x_742_, v_m_743_, v_a_744_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_inc(v_b_u2080_745_);
return v_b_u2080_745_;
}
else
{
lean_object* v_val_747_; 
v_val_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_val_747_);
lean_dec_ref_known(v___x_746_, 1);
return v_val_747_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___boxed(lean_object* v_00_u03b1_748_, lean_object* v_00_u03b2_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_m_752_, lean_object* v_a_753_, lean_object* v_b_u2080_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_PersistentHashMap_findD(v_00_u03b1_748_, v_00_u03b2_749_, v_x_750_, v_x_751_, v_m_752_, v_a_753_, v_b_u2080_754_);
lean_dec(v_b_u2080_754_);
lean_dec_ref(v_m_752_);
return v_res_755_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_759_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__2));
v___x_760_ = lean_unsigned_to_nat(14u);
v___x_761_ = lean_unsigned_to_nat(178u);
v___x_762_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__1));
v___x_763_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__0));
v___x_764_ = l_mkPanicMessageWithDecl(v___x_763_, v___x_762_, v___x_761_, v___x_760_, v___x_759_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg(lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_inst_767_, lean_object* v_m_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_765_, v_x_766_, v_m_768_, v_a_769_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_772_ = l_panic___redArg(v_inst_767_, v___x_771_);
return v___x_772_;
}
else
{
lean_object* v_val_773_; 
v_val_773_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v___x_770_, 1);
return v_val_773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg___boxed(lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_inst_776_, lean_object* v_m_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_PersistentHashMap_find_x21___redArg(v_x_774_, v_x_775_, v_inst_776_, v_m_777_, v_a_778_);
lean_dec_ref(v_m_777_);
lean_dec(v_inst_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21(lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_inst_784_, lean_object* v_m_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_782_, v_x_783_, v_m_785_, v_a_786_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_789_ = l_panic___redArg(v_inst_784_, v___x_788_);
return v___x_789_;
}
else
{
lean_object* v_val_790_; 
v_val_790_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_val_790_);
lean_dec_ref_known(v___x_787_, 1);
return v_val_790_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___boxed(lean_object* v_00_u03b1_791_, lean_object* v_00_u03b2_792_, lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_inst_795_, lean_object* v_m_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_PersistentHashMap_find_x21(v_00_u03b1_791_, v_00_u03b2_792_, v_x_793_, v_x_794_, v_inst_795_, v_m_796_, v_a_797_);
lean_dec_ref(v_m_796_);
lean_dec(v_inst_795_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg(lean_object* v_inst_799_, lean_object* v_keys_800_, lean_object* v_vals_801_, lean_object* v_i_802_, lean_object* v_k_803_){
_start:
{
lean_object* v___x_804_; uint8_t v___x_805_; 
v___x_804_ = lean_array_get_size(v_keys_800_);
v___x_805_ = lean_nat_dec_lt(v_i_802_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec(v_k_803_);
lean_dec(v_i_802_);
lean_dec_ref(v_inst_799_);
v___x_806_ = lean_box(0);
return v___x_806_;
}
else
{
lean_object* v_k_x27_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_k_x27_807_ = lean_array_fget_borrowed(v_keys_800_, v_i_802_);
lean_inc_ref(v_inst_799_);
lean_inc(v_k_x27_807_);
lean_inc(v_k_803_);
v___x_808_ = lean_apply_2(v_inst_799_, v_k_803_, v_k_x27_807_);
v___x_809_ = lean_unbox(v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_unsigned_to_nat(1u);
v___x_811_ = lean_nat_add(v_i_802_, v___x_810_);
lean_dec(v_i_802_);
v_i_802_ = v___x_811_;
goto _start;
}
else
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v_k_803_);
lean_dec_ref(v_inst_799_);
v___x_813_ = lean_array_fget_borrowed(v_vals_801_, v_i_802_);
lean_dec(v_i_802_);
lean_inc(v___x_813_);
lean_inc(v_k_x27_807_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v_k_x27_807_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg___boxed(lean_object* v_inst_816_, lean_object* v_keys_817_, lean_object* v_vals_818_, lean_object* v_i_819_, lean_object* v_k_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_816_, v_keys_817_, v_vals_818_, v_i_819_, v_k_820_);
lean_dec_ref(v_vals_818_);
lean_dec_ref(v_keys_817_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux(lean_object* v_00_u03b1_822_, lean_object* v_00_u03b2_823_, lean_object* v_inst_824_, lean_object* v_keys_825_, lean_object* v_vals_826_, lean_object* v_heq_827_, lean_object* v_i_828_, lean_object* v_k_829_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_824_, v_keys_825_, v_vals_826_, v_i_828_, v_k_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___boxed(lean_object* v_00_u03b1_831_, lean_object* v_00_u03b2_832_, lean_object* v_inst_833_, lean_object* v_keys_834_, lean_object* v_vals_835_, lean_object* v_heq_836_, lean_object* v_i_837_, lean_object* v_k_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_PersistentHashMap_findEntryAtAux(v_00_u03b1_831_, v_00_u03b2_832_, v_inst_833_, v_keys_834_, v_vals_835_, v_heq_836_, v_i_837_, v_k_838_);
lean_dec_ref(v_vals_835_);
lean_dec_ref(v_keys_834_);
return v_res_839_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg(lean_object* v_inst_840_, lean_object* v_x_841_, size_t v_x_842_, lean_object* v_x_843_){
_start:
{
if (lean_obj_tag(v_x_841_) == 0)
{
lean_object* v_es_844_; lean_object* v___x_845_; size_t v___x_846_; size_t v___x_847_; lean_object* v_j_848_; lean_object* v___x_849_; 
v_es_844_ = lean_ctor_get(v_x_841_, 0);
lean_inc_ref(v_es_844_);
lean_dec_ref_known(v_x_841_, 1);
v___x_845_ = lean_box(2);
v___x_846_ = ((size_t)31ULL);
v___x_847_ = lean_usize_land(v_x_842_, v___x_846_);
v_j_848_ = lean_usize_to_nat(v___x_847_);
v___x_849_ = lean_array_get(v___x_845_, v_es_844_, v_j_848_);
lean_dec(v_j_848_);
lean_dec_ref(v_es_844_);
switch(lean_obj_tag(v___x_849_))
{
case 0:
{
lean_object* v_key_850_; lean_object* v_val_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_key_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc_n(v_key_850_, 2);
v_val_851_ = lean_ctor_get(v___x_849_, 1);
lean_inc(v_val_851_);
lean_dec_ref_known(v___x_849_, 2);
v___x_852_ = lean_apply_2(v_inst_840_, v_x_843_, v_key_850_);
v___x_853_ = lean_unbox(v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; 
lean_dec(v_val_851_);
lean_dec(v_key_850_);
v___x_854_ = lean_box(0);
return v___x_854_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v_key_850_);
lean_ctor_set(v___x_855_, 1, v_val_851_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
return v___x_856_;
}
}
case 1:
{
lean_object* v_node_857_; size_t v___x_858_; size_t v___x_859_; 
v_node_857_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_node_857_);
lean_dec_ref_known(v___x_849_, 1);
v___x_858_ = ((size_t)5ULL);
v___x_859_ = lean_usize_shift_right(v_x_842_, v___x_858_);
v_x_841_ = v_node_857_;
v_x_842_ = v___x_859_;
goto _start;
}
default: 
{
lean_object* v___x_861_; 
lean_dec(v_x_843_);
lean_dec_ref(v_inst_840_);
v___x_861_ = lean_box(0);
return v___x_861_;
}
}
}
else
{
lean_object* v_ks_862_; lean_object* v_vs_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_ks_862_ = lean_ctor_get(v_x_841_, 0);
lean_inc_ref(v_ks_862_);
v_vs_863_ = lean_ctor_get(v_x_841_, 1);
lean_inc_ref(v_vs_863_);
lean_dec_ref_known(v_x_841_, 2);
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_840_, v_ks_862_, v_vs_863_, v___x_864_, v_x_843_);
lean_dec_ref(v_vs_863_);
lean_dec_ref(v_ks_862_);
return v___x_865_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_840_ = stack[0].m_obj;
lean_object* v_x_841_ = stack[1].m_obj;
size_t v_x_842_ = stack[2].m_num;
lean_object* v_x_843_ = stack[3].m_obj;
lean_object* v_res_866_;
v_res_866_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_840_, v_x_841_, v_x_842_, v_x_843_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg___boxed(lean_object* v_inst_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
size_t v_x_121__boxed_871_; lean_object* v_res_872_; 
v_x_121__boxed_871_ = lean_unbox_usize(v_x_869_);
lean_dec(v_x_869_);
v_res_872_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_867_, v_x_868_, v_x_121__boxed_871_, v_x_870_);
return v_res_872_;
}
}
lean_object* l_Lean_PersistentHashMap_findEntryAux(lean_object* v_00_u03b1_873_, lean_object* v_00_u03b2_874_, lean_object* v_inst_875_, lean_object* v_x_876_, size_t v_x_877_, lean_object* v_x_878_){
_start:
{
lean_object* v___x_879_; 
lean_inc_ref(v_x_876_);
v___x_879_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_875_, v_x_876_, v_x_877_, v_x_878_);
return v___x_879_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findEntryAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_875_ = stack[2].m_obj;
lean_object* v_x_876_ = stack[3].m_obj;
size_t v_x_877_ = stack[4].m_num;
lean_object* v_x_878_ = stack[5].m_obj;
lean_object* v_res_880_;
v_res_880_ = l_Lean_PersistentHashMap_findEntryAux(lean_box(0), lean_box(0), v_inst_875_, v_x_876_, v_x_877_, v_x_878_);
stack->m_obj
 = v_res_880_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___boxed(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_inst_883_, lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_x_886_){
_start:
{
size_t v_x_204__boxed_887_; lean_object* v_res_888_; 
v_x_204__boxed_887_ = lean_unbox_usize(v_x_885_);
lean_dec(v_x_885_);
v_res_888_ = l_Lean_PersistentHashMap_findEntryAux(v_00_u03b1_881_, v_00_u03b2_882_, v_inst_883_, v_x_884_, v_x_204__boxed_887_, v_x_886_);
lean_dec_ref(v_x_884_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object* v_x_889_, lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v_x_892_){
_start:
{
lean_object* v___x_893_; uint64_t v___x_894_; size_t v___x_895_; lean_object* v___x_896_; 
lean_inc(v_x_892_);
v___x_893_ = lean_apply_1(v_x_890_, v_x_892_);
v___x_894_ = lean_unbox_uint64(v___x_893_);
lean_dec_ref(v___x_893_);
v___x_895_ = lean_uint64_to_usize(v___x_894_);
lean_inc_ref(v_x_891_);
v___x_896_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_x_889_, v_x_891_, v___x_895_, v_x_892_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg___boxed(lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_897_, v_x_898_, v_x_899_, v_x_900_);
lean_dec_ref(v_x_899_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_x_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_904_, v_x_905_, v_x_906_, v_x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___boxed(lean_object* v_00_u03b1_909_, lean_object* v_00_u03b2_910_, lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_PersistentHashMap_findEntry_x3f(v_00_u03b1_909_, v_00_u03b2_910_, v_x_911_, v_x_912_, v_x_913_, v_x_914_);
lean_dec_ref(v_x_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg(lean_object* v_inst_916_, lean_object* v_keys_917_, lean_object* v_i_918_, lean_object* v_k_919_, lean_object* v_k_u2080_920_){
_start:
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = lean_array_get_size(v_keys_917_);
v___x_922_ = lean_nat_dec_lt(v_i_918_, v___x_921_);
if (v___x_922_ == 0)
{
lean_dec(v_k_919_);
lean_dec(v_i_918_);
lean_dec_ref(v_inst_916_);
lean_inc(v_k_u2080_920_);
return v_k_u2080_920_;
}
else
{
lean_object* v_k_x27_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_k_x27_923_ = lean_array_fget_borrowed(v_keys_917_, v_i_918_);
lean_inc_ref(v_inst_916_);
lean_inc(v_k_x27_923_);
lean_inc(v_k_919_);
v___x_924_ = lean_apply_2(v_inst_916_, v_k_919_, v_k_x27_923_);
v___x_925_ = lean_unbox(v___x_924_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_add(v_i_918_, v___x_926_);
lean_dec(v_i_918_);
v_i_918_ = v___x_927_;
goto _start;
}
else
{
lean_dec(v_k_919_);
lean_dec(v_i_918_);
lean_dec_ref(v_inst_916_);
lean_inc(v_k_x27_923_);
return v_k_x27_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg___boxed(lean_object* v_inst_929_, lean_object* v_keys_930_, lean_object* v_i_931_, lean_object* v_k_932_, lean_object* v_k_u2080_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_929_, v_keys_930_, v_i_931_, v_k_932_, v_k_u2080_933_);
lean_dec(v_k_u2080_933_);
lean_dec_ref(v_keys_930_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_inst_937_, lean_object* v_keys_938_, lean_object* v_vals_939_, lean_object* v_heq_940_, lean_object* v_i_941_, lean_object* v_k_942_, lean_object* v_k_u2080_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_937_, v_keys_938_, v_i_941_, v_k_942_, v_k_u2080_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___boxed(lean_object* v_00_u03b1_945_, lean_object* v_00_u03b2_946_, lean_object* v_inst_947_, lean_object* v_keys_948_, lean_object* v_vals_949_, lean_object* v_heq_950_, lean_object* v_i_951_, lean_object* v_k_952_, lean_object* v_k_u2080_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_PersistentHashMap_findKeyDAtAux(v_00_u03b1_945_, v_00_u03b2_946_, v_inst_947_, v_keys_948_, v_vals_949_, v_heq_950_, v_i_951_, v_k_952_, v_k_u2080_953_);
lean_dec(v_k_u2080_953_);
lean_dec_ref(v_vals_949_);
lean_dec_ref(v_keys_948_);
return v_res_954_;
}
}
lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object* v_inst_955_, lean_object* v_x_956_, size_t v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
if (lean_obj_tag(v_x_956_) == 0)
{
lean_object* v_es_960_; lean_object* v___x_961_; size_t v___x_962_; size_t v___x_963_; lean_object* v_j_964_; lean_object* v___x_965_; 
v_es_960_ = lean_ctor_get(v_x_956_, 0);
lean_inc_ref(v_es_960_);
lean_dec_ref_known(v_x_956_, 1);
v___x_961_ = lean_box(2);
v___x_962_ = ((size_t)31ULL);
v___x_963_ = lean_usize_land(v_x_957_, v___x_962_);
v_j_964_ = lean_usize_to_nat(v___x_963_);
v___x_965_ = lean_array_get(v___x_961_, v_es_960_, v_j_964_);
lean_dec(v_j_964_);
lean_dec_ref(v_es_960_);
switch(lean_obj_tag(v___x_965_))
{
case 0:
{
lean_object* v_key_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_key_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc_n(v_key_966_, 2);
lean_dec_ref_known(v___x_965_, 2);
v___x_967_ = lean_apply_2(v_inst_955_, v_x_958_, v_key_966_);
v___x_968_ = lean_unbox(v___x_967_);
if (v___x_968_ == 0)
{
lean_dec(v_key_966_);
lean_inc(v_x_959_);
return v_x_959_;
}
else
{
return v_key_966_;
}
}
case 1:
{
lean_object* v_node_969_; size_t v___x_970_; size_t v___x_971_; 
v_node_969_ = lean_ctor_get(v___x_965_, 0);
lean_inc(v_node_969_);
lean_dec_ref_known(v___x_965_, 1);
v___x_970_ = ((size_t)5ULL);
v___x_971_ = lean_usize_shift_right(v_x_957_, v___x_970_);
v_x_956_ = v_node_969_;
v_x_957_ = v___x_971_;
goto _start;
}
default: 
{
lean_dec(v_x_958_);
lean_dec_ref(v_inst_955_);
lean_inc(v_x_959_);
return v_x_959_;
}
}
}
else
{
lean_object* v_ks_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_ks_973_ = lean_ctor_get(v_x_956_, 0);
lean_inc_ref(v_ks_973_);
lean_dec_ref_known(v_x_956_, 2);
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_955_, v_ks_973_, v___x_974_, v_x_958_, v_x_959_);
lean_dec_ref(v_ks_973_);
return v___x_975_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findKeyDAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_955_ = stack[0].m_obj;
lean_object* v_x_956_ = stack[1].m_obj;
size_t v_x_957_ = stack[2].m_num;
lean_object* v_x_958_ = stack[3].m_obj;
lean_object* v_x_959_ = stack[4].m_obj;
lean_object* v_res_976_;
v_res_976_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_955_, v_x_956_, v_x_957_, v_x_958_, v_x_959_);
stack->m_obj
 = v_res_976_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg___boxed(lean_object* v_inst_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
size_t v_x_113__boxed_982_; lean_object* v_res_983_; 
v_x_113__boxed_982_ = lean_unbox_usize(v_x_979_);
lean_dec(v_x_979_);
v_res_983_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_977_, v_x_978_, v_x_113__boxed_982_, v_x_980_, v_x_981_);
lean_dec(v_x_981_);
return v_res_983_;
}
}
lean_object* l_Lean_PersistentHashMap_findKeyDAux(lean_object* v_00_u03b1_984_, lean_object* v_00_u03b2_985_, lean_object* v_inst_986_, lean_object* v_x_987_, size_t v_x_988_, lean_object* v_x_989_, lean_object* v_x_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_986_, v_x_987_, v_x_988_, v_x_989_, v_x_990_);
return v___x_991_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findKeyDAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_986_ = stack[2].m_obj;
lean_object* v_x_987_ = stack[3].m_obj;
size_t v_x_988_ = stack[4].m_num;
lean_object* v_x_989_ = stack[5].m_obj;
lean_object* v_x_990_ = stack[6].m_obj;
lean_object* v_res_992_;
v_res_992_ = l_Lean_PersistentHashMap_findKeyDAux(lean_box(0), lean_box(0), v_inst_986_, v_x_987_, v_x_988_, v_x_989_, v_x_990_);
stack->m_obj
 = v_res_992_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___boxed(lean_object* v_00_u03b1_993_, lean_object* v_00_u03b2_994_, lean_object* v_inst_995_, lean_object* v_x_996_, lean_object* v_x_997_, lean_object* v_x_998_, lean_object* v_x_999_){
_start:
{
size_t v_x_185__boxed_1000_; lean_object* v_res_1001_; 
v_x_185__boxed_1000_ = lean_unbox_usize(v_x_997_);
lean_dec(v_x_997_);
v_res_1001_ = l_Lean_PersistentHashMap_findKeyDAux(v_00_u03b1_993_, v_00_u03b2_994_, v_inst_995_, v_x_996_, v_x_185__boxed_1000_, v_x_998_, v_x_999_);
lean_dec(v_x_999_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg(lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_m_1004_, lean_object* v_a_1005_, lean_object* v_a_u2080_1006_){
_start:
{
lean_object* v___x_1007_; uint64_t v___x_1008_; size_t v___x_1009_; lean_object* v___x_1010_; 
lean_inc(v_a_1005_);
v___x_1007_ = lean_apply_1(v_x_1003_, v_a_1005_);
v___x_1008_ = lean_unbox_uint64(v___x_1007_);
lean_dec_ref(v___x_1007_);
v___x_1009_ = lean_uint64_to_usize(v___x_1008_);
v___x_1010_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_1002_, v_m_1004_, v___x_1009_, v_a_1005_, v_a_u2080_1006_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg___boxed(lean_object* v_x_1011_, lean_object* v_x_1012_, lean_object* v_m_1013_, lean_object* v_a_1014_, lean_object* v_a_u2080_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_PersistentHashMap_findKeyD___redArg(v_x_1011_, v_x_1012_, v_m_1013_, v_a_1014_, v_a_u2080_1015_);
lean_dec(v_a_u2080_1015_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD(lean_object* v_00_u03b1_1017_, lean_object* v_00_u03b2_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_, lean_object* v_m_1021_, lean_object* v_a_1022_, lean_object* v_a_u2080_1023_){
_start:
{
lean_object* v___x_1024_; uint64_t v___x_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
lean_inc(v_a_1022_);
v___x_1024_ = lean_apply_1(v_x_1020_, v_a_1022_);
v___x_1025_ = lean_unbox_uint64(v___x_1024_);
lean_dec_ref(v___x_1024_);
v___x_1026_ = lean_uint64_to_usize(v___x_1025_);
v___x_1027_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_1019_, v_m_1021_, v___x_1026_, v_a_1022_, v_a_u2080_1023_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_00_u03b2_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_m_1032_, lean_object* v_a_1033_, lean_object* v_a_u2080_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l_Lean_PersistentHashMap_findKeyD(v_00_u03b1_1028_, v_00_u03b2_1029_, v_x_1030_, v_x_1031_, v_m_1032_, v_a_1033_, v_a_u2080_1034_);
lean_dec(v_a_u2080_1034_);
return v_res_1035_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___redArg(lean_object* v_inst_1036_, lean_object* v_keys_1037_, lean_object* v_i_1038_, lean_object* v_k_1039_){
_start:
{
lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1040_ = lean_array_get_size(v_keys_1037_);
v___x_1041_ = lean_nat_dec_lt(v_i_1038_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_dec(v_k_1039_);
lean_dec(v_i_1038_);
lean_dec_ref(v_inst_1036_);
return v___x_1041_;
}
else
{
lean_object* v_k_x27_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_k_x27_1042_ = lean_array_fget_borrowed(v_keys_1037_, v_i_1038_);
lean_inc_ref(v_inst_1036_);
lean_inc(v_k_x27_1042_);
lean_inc(v_k_1039_);
v___x_1043_ = lean_apply_2(v_inst_1036_, v_k_1039_, v_k_x27_1042_);
v___x_1044_ = lean_unbox(v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_add(v_i_1038_, v___x_1045_);
lean_dec(v_i_1038_);
v_i_1038_ = v___x_1046_;
goto _start;
}
else
{
lean_dec(v_k_1039_);
lean_dec(v_i_1038_);
lean_dec_ref(v_inst_1036_);
return v___x_1041_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1036_ = stack[0].m_obj;
lean_object* v_keys_1037_ = stack[1].m_obj;
lean_object* v_i_1038_ = stack[2].m_obj;
lean_object* v_k_1039_ = stack[3].m_obj;
uint8_t v_res_1048_;
v_res_1048_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1036_, v_keys_1037_, v_i_1038_, v_k_1039_);
stack->m_num = v_res_1048_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___redArg___boxed(lean_object* v_inst_1049_, lean_object* v_keys_1050_, lean_object* v_i_1051_, lean_object* v_k_1052_){
_start:
{
uint8_t v_res_1053_; lean_object* v_r_1054_; 
v_res_1053_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1049_, v_keys_1050_, v_i_1051_, v_k_1052_);
lean_dec_ref(v_keys_1050_);
v_r_1054_ = lean_box(v_res_1053_);
return v_r_1054_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux(lean_object* v_00_u03b1_1055_, lean_object* v_00_u03b2_1056_, lean_object* v_inst_1057_, lean_object* v_keys_1058_, lean_object* v_vals_1059_, lean_object* v_heq_1060_, lean_object* v_i_1061_, lean_object* v_k_1062_){
_start:
{
uint8_t v___x_1063_; 
v___x_1063_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1057_, v_keys_1058_, v_i_1061_, v_k_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1057_ = stack[2].m_obj;
lean_object* v_keys_1058_ = stack[3].m_obj;
lean_object* v_vals_1059_ = stack[4].m_obj;
lean_object* v_i_1061_ = stack[6].m_obj;
lean_object* v_k_1062_ = stack[7].m_obj;
uint8_t v_res_1064_;
v_res_1064_ = l_Lean_PersistentHashMap_containsAtAux(lean_box(0), lean_box(0), v_inst_1057_, v_keys_1058_, v_vals_1059_, lean_box(0), v_i_1061_, v_k_1062_);
stack->m_num = v_res_1064_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___boxed(lean_object* v_00_u03b1_1065_, lean_object* v_00_u03b2_1066_, lean_object* v_inst_1067_, lean_object* v_keys_1068_, lean_object* v_vals_1069_, lean_object* v_heq_1070_, lean_object* v_i_1071_, lean_object* v_k_1072_){
_start:
{
uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Lean_PersistentHashMap_containsAtAux(v_00_u03b1_1065_, v_00_u03b2_1066_, v_inst_1067_, v_keys_1068_, v_vals_1069_, v_heq_1070_, v_i_1071_, v_k_1072_);
lean_dec_ref(v_vals_1069_);
lean_dec_ref(v_keys_1068_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___redArg(lean_object* v_inst_1075_, lean_object* v_x_1076_, size_t v_x_1077_, lean_object* v_x_1078_){
_start:
{
if (lean_obj_tag(v_x_1076_) == 0)
{
lean_object* v_es_1079_; lean_object* v___x_1080_; size_t v___x_1081_; size_t v___x_1082_; lean_object* v_j_1083_; lean_object* v___x_1084_; 
v_es_1079_ = lean_ctor_get(v_x_1076_, 0);
lean_inc_ref(v_es_1079_);
lean_dec_ref_known(v_x_1076_, 1);
v___x_1080_ = lean_box(2);
v___x_1081_ = ((size_t)31ULL);
v___x_1082_ = lean_usize_land(v_x_1077_, v___x_1081_);
v_j_1083_ = lean_usize_to_nat(v___x_1082_);
v___x_1084_ = lean_array_get(v___x_1080_, v_es_1079_, v_j_1083_);
lean_dec(v_j_1083_);
lean_dec_ref(v_es_1079_);
switch(lean_obj_tag(v___x_1084_))
{
case 0:
{
lean_object* v_key_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v_key_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_key_1085_);
lean_dec_ref_known(v___x_1084_, 2);
v___x_1086_ = lean_apply_2(v_inst_1075_, v_x_1078_, v_key_1085_);
v___x_1087_ = lean_unbox(v___x_1086_);
return v___x_1087_;
}
case 1:
{
lean_object* v_node_1088_; size_t v___x_1089_; size_t v___x_1090_; 
v_node_1088_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_node_1088_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1089_ = ((size_t)5ULL);
v___x_1090_ = lean_usize_shift_right(v_x_1077_, v___x_1089_);
v_x_1076_ = v_node_1088_;
v_x_1077_ = v___x_1090_;
goto _start;
}
default: 
{
uint8_t v___x_1092_; 
lean_dec(v_x_1078_);
lean_dec_ref(v_inst_1075_);
v___x_1092_ = 0;
return v___x_1092_;
}
}
}
else
{
lean_object* v_ks_1093_; lean_object* v___x_1094_; uint8_t v___x_1095_; 
v_ks_1093_ = lean_ctor_get(v_x_1076_, 0);
lean_inc_ref(v_ks_1093_);
lean_dec_ref_known(v_x_1076_, 2);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1075_, v_ks_1093_, v___x_1094_, v_x_1078_);
lean_dec_ref(v_ks_1093_);
return v___x_1095_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1075_ = stack[0].m_obj;
lean_object* v_x_1076_ = stack[1].m_obj;
size_t v_x_1077_ = stack[2].m_num;
lean_object* v_x_1078_ = stack[3].m_obj;
uint8_t v_res_1096_;
v_res_1096_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1075_, v_x_1076_, v_x_1077_, v_x_1078_);
stack->m_num = v_res_1096_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___redArg___boxed(lean_object* v_inst_1097_, lean_object* v_x_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
size_t v_x_104__boxed_1101_; uint8_t v_res_1102_; lean_object* v_r_1103_; 
v_x_104__boxed_1101_ = lean_unbox_usize(v_x_1099_);
lean_dec(v_x_1099_);
v_res_1102_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1097_, v_x_1098_, v_x_104__boxed_1101_, v_x_1100_);
v_r_1103_ = lean_box(v_res_1102_);
return v_r_1103_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_inst_1106_, lean_object* v_x_1107_, size_t v_x_1108_, lean_object* v_x_1109_){
_start:
{
uint8_t v___x_1110_; 
v___x_1110_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1106_, v_x_1107_, v_x_1108_, v_x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1106_ = stack[2].m_obj;
lean_object* v_x_1107_ = stack[3].m_obj;
size_t v_x_1108_ = stack[4].m_num;
lean_object* v_x_1109_ = stack[5].m_obj;
uint8_t v_res_1111_;
v_res_1111_ = l_Lean_PersistentHashMap_containsAux(lean_box(0), lean_box(0), v_inst_1106_, v_x_1107_, v_x_1108_, v_x_1109_);
stack->m_num = v_res_1111_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_00_u03b2_1113_, lean_object* v_inst_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
size_t v_x_174__boxed_1118_; uint8_t v_res_1119_; lean_object* v_r_1120_; 
v_x_174__boxed_1118_ = lean_unbox_usize(v_x_1116_);
lean_dec(v_x_1116_);
v_res_1119_ = l_Lean_PersistentHashMap_containsAux(v_00_u03b1_1112_, v_00_u03b2_1113_, v_inst_1114_, v_x_1115_, v_x_174__boxed_1118_, v_x_1117_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_x_1123_, lean_object* v_x_1124_){
_start:
{
lean_object* v___x_1125_; uint64_t v___x_1126_; size_t v___x_1127_; uint8_t v___x_1128_; 
lean_inc(v_x_1124_);
v___x_1125_ = lean_apply_1(v_inst_1122_, v_x_1124_);
v___x_1126_ = lean_unbox_uint64(v___x_1125_);
lean_dec_ref(v___x_1125_);
v___x_1127_ = lean_uint64_to_usize(v___x_1126_);
v___x_1128_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1121_, v_x_1123_, v___x_1127_, v_x_1124_);
return v___x_1128_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1121_ = stack[0].m_obj;
lean_object* v_inst_1122_ = stack[1].m_obj;
lean_object* v_x_1123_ = stack[2].m_obj;
lean_object* v_x_1124_ = stack[3].m_obj;
uint8_t v_res_1129_;
v_res_1129_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1121_, v_inst_1122_, v_x_1123_, v_x_1124_);
stack->m_num = v_res_1129_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___redArg___boxed(lean_object* v_inst_1130_, lean_object* v_inst_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
uint8_t v_res_1134_; lean_object* v_r_1135_; 
v_res_1134_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1130_, v_inst_1131_, v_x_1132_, v_x_1133_);
v_r_1135_ = lean_box(v_res_1134_);
return v_r_1135_;
}
}
uint8_t l_Lean_PersistentHashMap_contains(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
uint8_t v___x_1142_; 
v___x_1142_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1138_, v_inst_1139_, v_x_1140_, v_x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1138_ = stack[2].m_obj;
lean_object* v_inst_1139_ = stack[3].m_obj;
lean_object* v_x_1140_ = stack[4].m_obj;
lean_object* v_x_1141_ = stack[5].m_obj;
uint8_t v_res_1143_;
v_res_1143_ = l_Lean_PersistentHashMap_contains(lean_box(0), lean_box(0), v_inst_1138_, v_inst_1139_, v_x_1140_, v_x_1141_);
stack->m_num = v_res_1143_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___boxed(lean_object* v_00_u03b1_1144_, lean_object* v_00_u03b2_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
uint8_t v_res_1150_; lean_object* v_r_1151_; 
v_res_1150_ = l_Lean_PersistentHashMap_contains(v_00_u03b1_1144_, v_00_u03b2_1145_, v_inst_1146_, v_inst_1147_, v_x_1148_, v_x_1149_);
v_r_1151_ = lean_box(v_res_1150_);
return v_r_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg(lean_object* v_a_1152_, lean_object* v_i_1153_, lean_object* v_acc_1154_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_array_get_size(v_a_1152_);
v___x_1156_ = lean_nat_dec_lt(v_i_1153_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_dec(v_i_1153_);
return v_acc_1154_;
}
else
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_array_fget(v_a_1152_, v_i_1153_);
switch(lean_obj_tag(v___x_1157_))
{
case 0:
{
if (lean_obj_tag(v_acc_1154_) == 0)
{
lean_object* v_key_1158_; lean_object* v_val_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1170_; 
v_key_1158_ = lean_ctor_get(v___x_1157_, 0);
v_val_1159_ = lean_ctor_get(v___x_1157_, 1);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1161_ = v___x_1157_;
v_isShared_1162_ = v_isSharedCheck_1170_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_val_1159_);
lean_inc(v_key_1158_);
lean_dec(v___x_1157_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1170_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1163_ = lean_unsigned_to_nat(1u);
v___x_1164_ = lean_nat_add(v_i_1153_, v___x_1163_);
lean_dec(v_i_1153_);
if (v_isShared_1162_ == 0)
{
v___x_1166_ = v___x_1161_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_key_1158_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_val_1159_);
v___x_1166_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
v_i_1153_ = v___x_1164_;
v_acc_1154_ = v___x_1167_;
goto _start;
}
}
}
else
{
lean_object* v___x_1171_; 
lean_dec_ref_known(v_acc_1154_, 1);
lean_dec_ref_known(v___x_1157_, 2);
lean_dec(v_i_1153_);
v___x_1171_ = lean_box(0);
return v___x_1171_;
}
}
case 1:
{
lean_object* v___x_1172_; 
lean_dec_ref_known(v___x_1157_, 1);
lean_dec(v_acc_1154_);
lean_dec(v_i_1153_);
v___x_1172_ = lean_box(0);
return v___x_1172_;
}
default: 
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1173_ = lean_unsigned_to_nat(1u);
v___x_1174_ = lean_nat_add(v_i_1153_, v___x_1173_);
lean_dec(v_i_1153_);
v_i_1153_ = v___x_1174_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg___boxed(lean_object* v_a_1176_, lean_object* v_i_1177_, lean_object* v_acc_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1176_, v_i_1177_, v_acc_1178_);
lean_dec_ref(v_a_1176_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries(lean_object* v_00_u03b1_1180_, lean_object* v_00_u03b2_1181_, lean_object* v_a_1182_, lean_object* v_i_1183_, lean_object* v_acc_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1182_, v_i_1183_, v_acc_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___boxed(lean_object* v_00_u03b1_1186_, lean_object* v_00_u03b2_1187_, lean_object* v_a_1188_, lean_object* v_i_1189_, lean_object* v_acc_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_PersistentHashMap_isUnaryEntries(v_00_u03b1_1186_, v_00_u03b2_1187_, v_a_1188_, v_i_1189_, v_acc_1190_);
lean_dec_ref(v_a_1188_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object* v_x_1192_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
lean_object* v_es_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_es_1193_ = lean_ctor_get(v_x_1192_, 0);
lean_inc_ref(v_es_1193_);
lean_dec_ref_known(v_x_1192_, 1);
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_box(0);
v___x_1196_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_es_1193_, v___x_1194_, v___x_1195_);
lean_dec_ref(v_es_1193_);
return v___x_1196_;
}
else
{
lean_object* v_ks_1197_; lean_object* v_vs_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1213_; 
v_ks_1197_ = lean_ctor_get(v_x_1192_, 0);
v_vs_1198_ = lean_ctor_get(v_x_1192_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_x_1192_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1200_ = v_x_1192_;
v_isShared_1201_ = v_isSharedCheck_1213_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_vs_1198_);
lean_inc(v_ks_1197_);
lean_dec(v_x_1192_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1213_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1202_ = lean_unsigned_to_nat(1u);
v___x_1203_ = lean_array_get_size(v_ks_1197_);
v___x_1204_ = lean_nat_dec_eq(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; 
lean_del_object(v___x_1200_);
lean_dec_ref(v_vs_1198_);
lean_dec_ref(v_ks_1197_);
v___x_1205_ = lean_box(0);
return v___x_1205_;
}
else
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = lean_array_fget(v_ks_1197_, v___x_1206_);
lean_dec_ref(v_ks_1197_);
v___x_1208_ = lean_array_fget(v_vs_1198_, v___x_1206_);
lean_dec_ref(v_vs_1198_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set_tag(v___x_1200_, 0);
lean_ctor_set(v___x_1200_, 1, v___x_1208_);
lean_ctor_set(v___x_1200_, 0, v___x_1207_);
v___x_1210_ = v___x_1200_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode(lean_object* v_00_u03b1_1214_, lean_object* v_00_u03b2_1215_, lean_object* v_x_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_x_1216_);
return v___x_1217_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux___redArg(lean_object* v_inst_1218_, lean_object* v_x_1219_, size_t v_x_1220_, lean_object* v_x_1221_){
_start:
{
if (lean_obj_tag(v_x_1219_) == 0)
{
lean_object* v_es_1222_; lean_object* v___x_1223_; size_t v___x_1224_; size_t v___x_1225_; lean_object* v_j_1226_; lean_object* v_entry_1227_; 
v_es_1222_ = lean_ctor_get(v_x_1219_, 0);
v___x_1223_ = lean_box(2);
v___x_1224_ = ((size_t)31ULL);
v___x_1225_ = lean_usize_land(v_x_1220_, v___x_1224_);
v_j_1226_ = lean_usize_to_nat(v___x_1225_);
v_entry_1227_ = lean_array_get(v___x_1223_, v_es_1222_, v_j_1226_);
switch(lean_obj_tag(v_entry_1227_))
{
case 0:
{
lean_object* v_key_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v_key_1228_ = lean_ctor_get(v_entry_1227_, 0);
lean_inc(v_key_1228_);
lean_dec_ref_known(v_entry_1227_, 2);
v___x_1229_ = lean_apply_2(v_inst_1218_, v_x_1221_, v_key_1228_);
v___x_1230_ = lean_unbox(v___x_1229_);
if (v___x_1230_ == 0)
{
lean_dec(v_j_1226_);
return v_x_1219_;
}
else
{
lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1238_; 
lean_inc_ref(v_es_1222_);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_x_1219_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v_x_1219_, 0);
lean_dec(v_unused_1239_);
v___x_1232_ = v_x_1219_;
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
else
{
lean_dec(v_x_1219_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1238_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1234_ = lean_array_set(v_es_1222_, v_j_1226_, v___x_1223_);
lean_dec(v_j_1226_);
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v___x_1234_);
v___x_1236_ = v___x_1232_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
case 1:
{
lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1274_; 
lean_inc_ref(v_es_1222_);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_x_1219_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v_x_1219_, 0);
lean_dec(v_unused_1275_);
v___x_1241_ = v_x_1219_;
v_isShared_1242_ = v_isSharedCheck_1274_;
goto v_resetjp_1240_;
}
else
{
lean_dec(v_x_1219_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1274_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v_node_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1273_; 
v_node_1243_ = lean_ctor_get(v_entry_1227_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_entry_1227_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1245_ = v_entry_1227_;
v_isShared_1246_ = v_isSharedCheck_1273_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_node_1243_);
lean_dec(v_entry_1227_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1273_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
size_t v___x_1247_; lean_object* v_entries_1248_; size_t v___x_1249_; lean_object* v_newNode_1250_; lean_object* v___x_1251_; 
v___x_1247_ = ((size_t)5ULL);
v_entries_1248_ = lean_array_set(v_es_1222_, v_j_1226_, v___x_1223_);
v___x_1249_ = lean_usize_shift_right(v_x_1220_, v___x_1247_);
v_newNode_1250_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1218_, v_node_1243_, v___x_1249_, v_x_1221_);
lean_inc_ref(v_newNode_1250_);
v___x_1251_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1250_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_object* v___x_1253_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v_newNode_1250_);
v___x_1253_ = v___x_1245_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_newNode_1250_);
v___x_1253_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = lean_array_set(v_entries_1248_, v_j_1226_, v___x_1253_);
lean_dec(v_j_1226_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1254_);
v___x_1256_ = v___x_1241_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
else
{
lean_object* v_val_1259_; lean_object* v_fst_1260_; lean_object* v_snd_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1272_; 
lean_dec_ref(v_newNode_1250_);
lean_del_object(v___x_1245_);
v_val_1259_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v___x_1251_, 1);
v_fst_1260_ = lean_ctor_get(v_val_1259_, 0);
v_snd_1261_ = lean_ctor_get(v_val_1259_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_val_1259_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1263_ = v_val_1259_;
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_snd_1261_);
lean_inc(v_fst_1260_);
lean_dec(v_val_1259_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_fst_1260_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_snd_1261_);
v___x_1266_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_array_set(v_entries_1248_, v_j_1226_, v___x_1266_);
lean_dec(v_j_1226_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 0, v___x_1267_);
v___x_1269_ = v___x_1241_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_1226_);
lean_dec(v_x_1221_);
lean_dec_ref(v_inst_1218_);
return v_x_1219_;
}
}
}
else
{
lean_object* v_ks_1276_; lean_object* v_vs_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1291_; 
v_ks_1276_ = lean_ctor_get(v_x_1219_, 0);
v_vs_1277_ = lean_ctor_get(v_x_1219_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_x_1219_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1279_ = v_x_1219_;
v_isShared_1280_ = v_isSharedCheck_1291_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_vs_1277_);
lean_inc(v_ks_1276_);
lean_dec(v_x_1219_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1291_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Array_finIdxOf_x3f___redArg(v_inst_1218_, v_ks_1276_, v_x_1221_);
if (lean_obj_tag(v___x_1281_) == 0)
{
lean_object* v___x_1283_; 
if (v_isShared_1280_ == 0)
{
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_ks_1276_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_vs_1277_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
else
{
lean_object* v_val_1285_; lean_object* v_keys_x27_1286_; lean_object* v_vals_x27_1287_; lean_object* v___x_1289_; 
v_val_1285_ = lean_ctor_get(v___x_1281_, 0);
lean_inc_n(v_val_1285_, 2);
lean_dec_ref_known(v___x_1281_, 1);
v_keys_x27_1286_ = l_Array_eraseIdx___redArg(v_ks_1276_, v_val_1285_);
v_vals_x27_1287_ = l_Array_eraseIdx___redArg(v_vs_1277_, v_val_1285_);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v_vals_x27_1287_);
lean_ctor_set(v___x_1279_, 0, v_keys_x27_1286_);
v___x_1289_ = v___x_1279_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_keys_x27_1286_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_vals_x27_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1218_ = stack[0].m_obj;
lean_object* v_x_1219_ = stack[1].m_obj;
size_t v_x_1220_ = stack[2].m_num;
lean_object* v_x_1221_ = stack[3].m_obj;
lean_object* v_res_1292_;
v_res_1292_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1218_, v_x_1219_, v_x_1220_, v_x_1221_);
stack->m_obj
 = v_res_1292_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg___boxed(lean_object* v_inst_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_){
_start:
{
size_t v_x_202__boxed_1297_; lean_object* v_res_1298_; 
v_x_202__boxed_1297_ = lean_unbox_usize(v_x_1295_);
lean_dec(v_x_1295_);
v_res_1298_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1293_, v_x_1294_, v_x_202__boxed_1297_, v_x_1296_);
return v_res_1298_;
}
}
lean_object* l_Lean_PersistentHashMap_eraseAux(lean_object* v_00_u03b1_1299_, lean_object* v_00_u03b2_1300_, lean_object* v_inst_1301_, lean_object* v_x_1302_, size_t v_x_1303_, lean_object* v_x_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1301_, v_x_1302_, v_x_1303_, v_x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_eraseAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1301_ = stack[2].m_obj;
lean_object* v_x_1302_ = stack[3].m_obj;
size_t v_x_1303_ = stack[4].m_num;
lean_object* v_x_1304_ = stack[5].m_obj;
lean_object* v_res_1306_;
v_res_1306_ = l_Lean_PersistentHashMap_eraseAux(lean_box(0), lean_box(0), v_inst_1301_, v_x_1302_, v_x_1303_, v_x_1304_);
stack->m_obj
 = v_res_1306_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_00_u03b2_1308_, lean_object* v_inst_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_){
_start:
{
size_t v_x_415__boxed_1313_; lean_object* v_res_1314_; 
v_x_415__boxed_1313_ = lean_unbox_usize(v_x_1311_);
lean_dec(v_x_1311_);
v_res_1314_ = l_Lean_PersistentHashMap_eraseAux(v_00_u03b1_1307_, v_00_u03b2_1308_, v_inst_1309_, v_x_1310_, v_x_415__boxed_1313_, v_x_1312_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object* v_x_1315_, lean_object* v_x_1316_, lean_object* v_x_1317_, lean_object* v_x_1318_){
_start:
{
lean_object* v___x_1319_; uint64_t v___x_1320_; size_t v_h_1321_; lean_object* v___x_1322_; 
lean_inc(v_x_1318_);
v___x_1319_ = lean_apply_1(v_x_1316_, v_x_1318_);
v___x_1320_ = lean_unbox_uint64(v___x_1319_);
lean_dec_ref(v___x_1319_);
v_h_1321_ = lean_uint64_to_usize(v___x_1320_);
v___x_1322_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_x_1315_, v_x_1317_, v_h_1321_, v_x_1318_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase(lean_object* v_00_u03b1_1323_, lean_object* v_00_u03b2_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_, lean_object* v_x_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_PersistentHashMap_erase___redArg(v_x_1325_, v_x_1326_, v_x_1327_, v_x_1328_);
return v___x_1329_;
}
}
lean_object* l_Lean_PersistentHashMap_alterAux___redArg(lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_f_1332_, lean_object* v_x_1333_, size_t v_x_1334_, size_t v_x_1335_, lean_object* v_x_1336_){
_start:
{
if (lean_obj_tag(v_x_1333_) == 0)
{
lean_object* v_es_1337_; size_t v___x_1338_; size_t v___x_1339_; lean_object* v_j_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_es_1337_ = lean_ctor_get(v_x_1333_, 0);
v___x_1338_ = ((size_t)31ULL);
v___x_1339_ = lean_usize_land(v_x_1334_, v___x_1338_);
v_j_1340_ = lean_usize_to_nat(v___x_1339_);
v___x_1341_ = lean_array_get_size(v_es_1337_);
v___x_1342_ = lean_nat_dec_lt(v_j_1340_, v___x_1341_);
if (v___x_1342_ == 0)
{
lean_dec(v_j_1340_);
lean_dec(v_x_1336_);
lean_dec_ref(v_f_1332_);
lean_dec_ref(v_inst_1331_);
lean_dec_ref(v_inst_1330_);
return v_x_1333_;
}
else
{
lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1411_; 
lean_inc_ref(v_es_1337_);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_x_1333_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v_x_1333_, 0);
lean_dec(v_unused_1412_);
v___x_1344_ = v_x_1333_;
v_isShared_1345_ = v_isSharedCheck_1411_;
goto v_resetjp_1343_;
}
else
{
lean_dec(v_x_1333_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1411_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v_v_1346_; lean_object* v___x_1347_; lean_object* v_xs_x27_1348_; lean_object* v___y_1350_; 
v_v_1346_ = lean_array_fget(v_es_1337_, v_j_1340_);
v___x_1347_ = lean_box(0);
v_xs_x27_1348_ = lean_array_fset(v_es_1337_, v_j_1340_, v___x_1347_);
switch(lean_obj_tag(v_v_1346_))
{
case 0:
{
lean_object* v_key_1355_; lean_object* v_val_1356_; lean_object* v___x_1357_; uint8_t v___x_1358_; 
lean_dec_ref(v_inst_1331_);
v_key_1355_ = lean_ctor_get(v_v_1346_, 0);
v_val_1356_ = lean_ctor_get(v_v_1346_, 1);
lean_inc(v_key_1355_);
lean_inc(v_x_1336_);
v___x_1357_ = lean_apply_2(v_inst_1330_, v_x_1336_, v_key_1355_);
v___x_1358_ = lean_unbox(v___x_1357_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_apply_1(v_f_1332_, v___x_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_dec(v_x_1336_);
v___y_1350_ = v_v_1346_;
goto v___jp_1349_;
}
else
{
lean_object* v_val_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1369_; 
lean_inc(v_val_1356_);
lean_inc(v_key_1355_);
lean_dec_ref_known(v_v_1346_, 2);
v_val_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_val_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1355_, v_val_1356_, v_x_1336_, v_val_1361_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 0, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
v___y_1350_ = v___x_1367_;
goto v___jp_1349_;
}
}
}
}
else
{
lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1380_; 
lean_inc(v_val_1356_);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_v_1346_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; lean_object* v_unused_1382_; 
v_unused_1381_ = lean_ctor_get(v_v_1346_, 1);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v_v_1346_, 0);
lean_dec(v_unused_1382_);
v___x_1371_ = v_v_1346_;
v_isShared_1372_ = v_isSharedCheck_1380_;
goto v_resetjp_1370_;
}
else
{
lean_dec(v_v_1346_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1380_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v_val_1356_);
v___x_1374_ = lean_apply_1(v_f_1332_, v___x_1373_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v___x_1375_; 
lean_del_object(v___x_1371_);
lean_dec(v_x_1336_);
v___x_1375_ = lean_box(2);
v___y_1350_ = v___x_1375_;
goto v___jp_1349_;
}
else
{
lean_object* v_val_1376_; lean_object* v___x_1378_; 
v_val_1376_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v___x_1374_, 1);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v_val_1376_);
lean_ctor_set(v___x_1371_, 0, v_x_1336_);
v___x_1378_ = v___x_1371_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_x_1336_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_val_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
v___y_1350_ = v___x_1378_;
goto v___jp_1349_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1406_; 
v_node_1383_ = lean_ctor_get(v_v_1346_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_v_1346_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1385_ = v_v_1346_;
v_isShared_1386_ = v_isSharedCheck_1406_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_node_1383_);
lean_dec(v_v_1346_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1406_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
size_t v___x_1387_; size_t v___x_1388_; size_t v___x_1389_; size_t v___x_1390_; lean_object* v_newNode_1391_; lean_object* v___x_1392_; 
v___x_1387_ = ((size_t)5ULL);
v___x_1388_ = lean_usize_shift_right(v_x_1334_, v___x_1387_);
v___x_1389_ = ((size_t)1ULL);
v___x_1390_ = lean_usize_add(v_x_1335_, v___x_1389_);
v_newNode_1391_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1330_, v_inst_1331_, v_f_1332_, v_node_1383_, v___x_1388_, v___x_1390_, v_x_1336_);
lean_inc_ref(v_newNode_1391_);
v___x_1392_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1391_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v___x_1394_; 
if (v_isShared_1386_ == 0)
{
lean_ctor_set(v___x_1385_, 0, v_newNode_1391_);
v___x_1394_ = v___x_1385_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_newNode_1391_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
v___y_1350_ = v___x_1394_;
goto v___jp_1349_;
}
}
else
{
lean_object* v_val_1396_; lean_object* v_fst_1397_; lean_object* v_snd_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v_newNode_1391_);
lean_del_object(v___x_1385_);
v_val_1396_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_val_1396_);
lean_dec_ref_known(v___x_1392_, 1);
v_fst_1397_ = lean_ctor_get(v_val_1396_, 0);
v_snd_1398_ = lean_ctor_get(v_val_1396_, 1);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_val_1396_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v_val_1396_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_snd_1398_);
lean_inc(v_fst_1397_);
lean_dec(v_val_1396_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_fst_1397_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_snd_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
v___y_1350_ = v___x_1403_;
goto v___jp_1349_;
}
}
}
}
}
default: 
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec_ref(v_inst_1331_);
lean_dec_ref(v_inst_1330_);
v___x_1407_ = lean_box(0);
v___x_1408_ = lean_apply_1(v_f_1332_, v___x_1407_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_dec(v_x_1336_);
v___y_1350_ = v_v_1346_;
goto v___jp_1349_;
}
else
{
lean_object* v_val_1409_; lean_object* v___x_1410_; 
v_val_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_val_1409_);
lean_dec_ref_known(v___x_1408_, 1);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v_x_1336_);
lean_ctor_set(v___x_1410_, 1, v_val_1409_);
v___y_1350_ = v___x_1410_;
goto v___jp_1349_;
}
}
}
v___jp_1349_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_array_fset(v_xs_x27_1348_, v_j_1340_, v___y_1350_);
lean_dec(v_j_1340_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1351_);
v___x_1353_ = v___x_1344_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1351_);
v___x_1353_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
return v___x_1353_;
}
}
}
}
}
else
{
lean_object* v_ks_1413_; lean_object* v_vs_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1447_; 
v_ks_1413_ = lean_ctor_get(v_x_1333_, 0);
v_vs_1414_ = lean_ctor_get(v_x_1333_, 1);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_x_1333_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1416_ = v_x_1333_;
v_isShared_1417_ = v_isSharedCheck_1447_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_vs_1414_);
lean_inc(v_ks_1413_);
lean_dec(v_x_1333_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1447_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; 
lean_inc(v_x_1336_);
lean_inc_ref(v_inst_1330_);
v___x_1418_ = l_Array_finIdxOf_x3f___redArg(v_inst_1330_, v_ks_1413_, v_x_1336_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v___x_1420_; 
if (v_isShared_1417_ == 0)
{
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_ks_1413_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_vs_1414_);
v___x_1420_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = lean_box(0);
v___x_1422_ = lean_apply_1(v_f_1332_, v___x_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_dec(v_x_1336_);
lean_dec_ref(v_inst_1331_);
lean_dec_ref(v_inst_1330_);
return v___x_1420_;
}
else
{
lean_object* v_val_1423_; lean_object* v___x_1424_; 
v_val_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_val_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1424_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_1330_, v_inst_1331_, v___x_1420_, v_x_1334_, v_x_1335_, v_x_1336_, v_val_1423_);
return v___x_1424_;
}
}
}
else
{
lean_object* v_val_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1446_; 
lean_dec_ref(v_inst_1331_);
lean_dec_ref(v_inst_1330_);
v_val_1426_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1428_ = v___x_1418_;
v_isShared_1429_ = v_isSharedCheck_1446_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_val_1426_);
lean_dec(v___x_1418_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1446_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v_v_x27_1430_; lean_object* v_keys_1431_; lean_object* v_vals_1432_; lean_object* v___x_1434_; 
v_v_x27_1430_ = lean_array_fget(v_vs_1414_, v_val_1426_);
lean_inc(v_val_1426_);
v_keys_1431_ = l_Array_eraseIdx___redArg(v_ks_1413_, v_val_1426_);
v_vals_1432_ = l_Array_eraseIdx___redArg(v_vs_1414_, v_val_1426_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v_v_x27_1430_);
v___x_1434_ = v___x_1428_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_v_x27_1430_);
v___x_1434_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_apply_1(v_f_1332_, v___x_1434_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v___x_1437_; 
lean_dec(v_x_1336_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 1, v_vals_1432_);
lean_ctor_set(v___x_1416_, 0, v_keys_1431_);
v___x_1437_ = v___x_1416_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_keys_1431_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_vals_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
else
{
lean_object* v_val_1439_; lean_object* v_keys_1440_; lean_object* v_vals_1441_; lean_object* v___x_1443_; 
v_val_1439_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1439_);
lean_dec_ref_known(v___x_1435_, 1);
v_keys_1440_ = lean_array_push(v_keys_1431_, v_x_1336_);
v_vals_1441_ = lean_array_push(v_vals_1432_, v_val_1439_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 1, v_vals_1441_);
lean_ctor_set(v___x_1416_, 0, v_keys_1440_);
v___x_1443_ = v___x_1416_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_keys_1440_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_vals_1441_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_alterAux___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1330_ = stack[0].m_obj;
lean_object* v_inst_1331_ = stack[1].m_obj;
lean_object* v_f_1332_ = stack[2].m_obj;
lean_object* v_x_1333_ = stack[3].m_obj;
size_t v_x_1334_ = stack[4].m_num;
size_t v_x_1335_ = stack[5].m_num;
lean_object* v_x_1336_ = stack[6].m_obj;
lean_object* v_res_1448_;
v_res_1448_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1330_, v_inst_1331_, v_f_1332_, v_x_1333_, v_x_1334_, v_x_1335_, v_x_1336_);
stack->m_obj
 = v_res_1448_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg___boxed(lean_object* v_inst_1449_, lean_object* v_inst_1450_, lean_object* v_f_1451_, lean_object* v_x_1452_, lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v_x_1455_){
_start:
{
size_t v_x_413__boxed_1456_; size_t v_x_414__boxed_1457_; lean_object* v_res_1458_; 
v_x_413__boxed_1456_ = lean_unbox_usize(v_x_1453_);
lean_dec(v_x_1453_);
v_x_414__boxed_1457_ = lean_unbox_usize(v_x_1454_);
lean_dec(v_x_1454_);
v_res_1458_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1449_, v_inst_1450_, v_f_1451_, v_x_1452_, v_x_413__boxed_1456_, v_x_414__boxed_1457_, v_x_1455_);
return v_res_1458_;
}
}
lean_object* l_Lean_PersistentHashMap_alterAux(lean_object* v_00_u03b1_1459_, lean_object* v_00_u03b2_1460_, lean_object* v_inst_1461_, lean_object* v_inst_1462_, lean_object* v_f_1463_, lean_object* v_x_1464_, size_t v_x_1465_, size_t v_x_1466_, lean_object* v_x_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1461_, v_inst_1462_, v_f_1463_, v_x_1464_, v_x_1465_, v_x_1466_, v_x_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_alterAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1461_ = stack[2].m_obj;
lean_object* v_inst_1462_ = stack[3].m_obj;
lean_object* v_f_1463_ = stack[4].m_obj;
lean_object* v_x_1464_ = stack[5].m_obj;
size_t v_x_1465_ = stack[6].m_num;
size_t v_x_1466_ = stack[7].m_num;
lean_object* v_x_1467_ = stack[8].m_obj;
lean_object* v_res_1469_;
v_res_1469_ = l_Lean_PersistentHashMap_alterAux(lean_box(0), lean_box(0), v_inst_1461_, v_inst_1462_, v_f_1463_, v_x_1464_, v_x_1465_, v_x_1466_, v_x_1467_);
stack->m_obj
 = v_res_1469_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___boxed(lean_object* v_00_u03b1_1470_, lean_object* v_00_u03b2_1471_, lean_object* v_inst_1472_, lean_object* v_inst_1473_, lean_object* v_f_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_, lean_object* v_x_1477_, lean_object* v_x_1478_){
_start:
{
size_t v_x_749__boxed_1479_; size_t v_x_750__boxed_1480_; lean_object* v_res_1481_; 
v_x_749__boxed_1479_ = lean_unbox_usize(v_x_1476_);
lean_dec(v_x_1476_);
v_x_750__boxed_1480_ = lean_unbox_usize(v_x_1477_);
lean_dec(v_x_1477_);
v_res_1481_ = l_Lean_PersistentHashMap_alterAux(v_00_u03b1_1470_, v_00_u03b2_1471_, v_inst_1472_, v_inst_1473_, v_f_1474_, v_x_1475_, v_x_749__boxed_1479_, v_x_750__boxed_1480_, v_x_1478_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter___redArg(lean_object* v_x_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_, lean_object* v_x_1485_, lean_object* v_x_1486_){
_start:
{
lean_object* v___x_1487_; uint64_t v___x_1488_; size_t v_h_1489_; size_t v___x_1490_; lean_object* v___x_1491_; 
lean_inc_ref(v_x_1483_);
lean_inc(v_x_1485_);
v___x_1487_ = lean_apply_1(v_x_1483_, v_x_1485_);
v___x_1488_ = lean_unbox_uint64(v___x_1487_);
lean_dec_ref(v___x_1487_);
v_h_1489_ = lean_uint64_to_usize(v___x_1488_);
v___x_1490_ = ((size_t)1ULL);
v___x_1491_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1482_, v_x_1483_, v_x_1486_, v_x_1484_, v_h_1489_, v___x_1490_, v_x_1485_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter(lean_object* v_00_u03b1_1492_, lean_object* v_00_u03b2_1493_, lean_object* v_x_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_x_1497_, lean_object* v_x_1498_){
_start:
{
lean_object* v___x_1499_; uint64_t v___x_1500_; size_t v_h_1501_; size_t v___x_1502_; lean_object* v___x_1503_; 
lean_inc_ref(v_x_1495_);
lean_inc(v_x_1497_);
v___x_1499_ = lean_apply_1(v_x_1495_, v_x_1497_);
v___x_1500_ = lean_unbox_uint64(v___x_1499_);
lean_dec_ref(v___x_1499_);
v_h_1501_ = lean_uint64_to_usize(v___x_1500_);
v___x_1502_ = ((size_t)1ULL);
v___x_1503_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1494_, v_x_1495_, v_x_1498_, v_x_1496_, v_h_1501_, v___x_1502_, v_x_1497_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed(lean_object* v_i_1504_, lean_object* v_inst_1505_, lean_object* v_f_1506_, lean_object* v_keys_1507_, lean_object* v_vals_1508_, lean_object* v_____do__lift_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(v_i_1504_, v_inst_1505_, v_f_1506_, v_keys_1507_, v_vals_1508_, v_____do__lift_1509_);
lean_dec(v_i_1504_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(lean_object* v_inst_1511_, lean_object* v_f_1512_, lean_object* v_keys_1513_, lean_object* v_vals_1514_, lean_object* v_i_1515_, lean_object* v_acc_1516_){
_start:
{
lean_object* v_toApplicative_1517_; lean_object* v_toBind_1518_; lean_object* v_toPure_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v_toApplicative_1517_ = lean_ctor_get(v_inst_1511_, 0);
v_toBind_1518_ = lean_ctor_get(v_inst_1511_, 1);
lean_inc(v_toBind_1518_);
v_toPure_1519_ = lean_ctor_get(v_toApplicative_1517_, 1);
v___x_1520_ = lean_array_get_size(v_keys_1513_);
v___x_1521_ = lean_nat_dec_lt(v_i_1515_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_inc(v_toPure_1519_);
lean_dec(v_toBind_1518_);
lean_dec(v_i_1515_);
lean_dec_ref(v_vals_1514_);
lean_dec_ref(v_keys_1513_);
lean_dec(v_f_1512_);
lean_dec_ref(v_inst_1511_);
v___x_1522_ = lean_apply_2(v_toPure_1519_, lean_box(0), v_acc_1516_);
return v___x_1522_;
}
else
{
lean_object* v___f_1523_; lean_object* v_k_1524_; lean_object* v_v_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_inc_ref(v_vals_1514_);
lean_inc_ref(v_keys_1513_);
lean_inc(v_f_1512_);
lean_inc(v_i_1515_);
v___f_1523_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1523_, 0, v_i_1515_);
lean_closure_set(v___f_1523_, 1, v_inst_1511_);
lean_closure_set(v___f_1523_, 2, v_f_1512_);
lean_closure_set(v___f_1523_, 3, v_keys_1513_);
lean_closure_set(v___f_1523_, 4, v_vals_1514_);
v_k_1524_ = lean_array_fget(v_keys_1513_, v_i_1515_);
lean_dec_ref(v_keys_1513_);
v_v_1525_ = lean_array_fget(v_vals_1514_, v_i_1515_);
lean_dec(v_i_1515_);
lean_dec_ref(v_vals_1514_);
v___x_1526_ = lean_apply_3(v_f_1512_, v_acc_1516_, v_k_1524_, v_v_1525_);
v___x_1527_ = lean_apply_4(v_toBind_1518_, lean_box(0), lean_box(0), v___x_1526_, v___f_1523_);
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(lean_object* v_i_1528_, lean_object* v_inst_1529_, lean_object* v_f_1530_, lean_object* v_keys_1531_, lean_object* v_vals_1532_, lean_object* v_____do__lift_1533_){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1534_ = lean_unsigned_to_nat(1u);
v___x_1535_ = lean_nat_add(v_i_1528_, v___x_1534_);
v___x_1536_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1529_, v_f_1530_, v_keys_1531_, v_vals_1532_, v___x_1535_, v_____do__lift_1533_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse(lean_object* v_m_1537_, lean_object* v_inst_1538_, lean_object* v_00_u03c3_1539_, lean_object* v_00_u03b1_1540_, lean_object* v_00_u03b2_1541_, lean_object* v_f_1542_, lean_object* v_keys_1543_, lean_object* v_vals_1544_, lean_object* v_heq_1545_, lean_object* v_i_1546_, lean_object* v_acc_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1538_, v_f_1542_, v_keys_1543_, v_vals_1544_, v_i_1546_, v_acc_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object* v_inst_1549_, lean_object* v_f_1550_, lean_object* v_x_1551_, lean_object* v_x_1552_){
_start:
{
if (lean_obj_tag(v_x_1551_) == 0)
{
lean_object* v_toApplicative_1553_; lean_object* v_toPure_1554_; lean_object* v_es_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_toApplicative_1553_ = lean_ctor_get(v_inst_1549_, 0);
v_toPure_1554_ = lean_ctor_get(v_toApplicative_1553_, 1);
v_es_1555_ = lean_ctor_get(v_x_1551_, 0);
lean_inc_ref(v_es_1555_);
lean_dec_ref_known(v_x_1551_, 1);
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = lean_array_get_size(v_es_1555_);
v___x_1558_ = lean_nat_dec_lt(v___x_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; 
lean_inc(v_toPure_1554_);
lean_dec_ref(v_es_1555_);
lean_dec(v_f_1550_);
lean_dec_ref(v_inst_1549_);
v___x_1559_ = lean_apply_2(v_toPure_1554_, lean_box(0), v_x_1552_);
return v___x_1559_;
}
else
{
lean_object* v___f_1560_; uint8_t v___x_1561_; 
lean_inc(v_toPure_1554_);
lean_inc_ref(v_inst_1549_);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1560_, 0, v_f_1550_);
lean_closure_set(v___f_1560_, 1, v_inst_1549_);
lean_closure_set(v___f_1560_, 2, v_toPure_1554_);
v___x_1561_ = lean_nat_dec_le(v___x_1557_, v___x_1557_);
if (v___x_1561_ == 0)
{
if (v___x_1558_ == 0)
{
lean_object* v___x_1562_; 
lean_inc(v_toPure_1554_);
lean_dec_ref(v___f_1560_);
lean_dec_ref(v_es_1555_);
lean_dec_ref(v_inst_1549_);
v___x_1562_ = lean_apply_2(v_toPure_1554_, lean_box(0), v_x_1552_);
return v___x_1562_;
}
else
{
size_t v___x_1563_; size_t v___x_1564_; lean_object* v___x_1565_; 
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = lean_usize_of_nat(v___x_1557_);
v___x_1565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1549_, v___f_1560_, v_es_1555_, v___x_1563_, v___x_1564_, v_x_1552_);
return v___x_1565_;
}
}
else
{
size_t v___x_1566_; size_t v___x_1567_; lean_object* v___x_1568_; 
v___x_1566_ = ((size_t)0ULL);
v___x_1567_ = lean_usize_of_nat(v___x_1557_);
v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1549_, v___f_1560_, v_es_1555_, v___x_1566_, v___x_1567_, v_x_1552_);
return v___x_1568_;
}
}
}
else
{
lean_object* v_ks_1569_; lean_object* v_vs_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_ks_1569_ = lean_ctor_get(v_x_1551_, 0);
lean_inc_ref(v_ks_1569_);
v_vs_1570_ = lean_ctor_get(v_x_1551_, 1);
lean_inc_ref(v_vs_1570_);
lean_dec_ref_known(v_x_1551_, 2);
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1549_, v_f_1550_, v_ks_1569_, v_vs_1570_, v___x_1571_, v_x_1552_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0(lean_object* v_f_1573_, lean_object* v_inst_1574_, lean_object* v_toPure_1575_, lean_object* v_acc_1576_, lean_object* v_entry_1577_){
_start:
{
switch(lean_obj_tag(v_entry_1577_))
{
case 0:
{
lean_object* v_key_1578_; lean_object* v_val_1579_; lean_object* v___x_1580_; 
lean_dec(v_toPure_1575_);
lean_dec_ref(v_inst_1574_);
v_key_1578_ = lean_ctor_get(v_entry_1577_, 0);
lean_inc(v_key_1578_);
v_val_1579_ = lean_ctor_get(v_entry_1577_, 1);
lean_inc(v_val_1579_);
lean_dec_ref_known(v_entry_1577_, 2);
v___x_1580_ = lean_apply_3(v_f_1573_, v_acc_1576_, v_key_1578_, v_val_1579_);
return v___x_1580_;
}
case 1:
{
lean_object* v_node_1581_; lean_object* v___x_1582_; 
lean_dec(v_toPure_1575_);
v_node_1581_ = lean_ctor_get(v_entry_1577_, 0);
lean_inc(v_node_1581_);
lean_dec_ref_known(v_entry_1577_, 1);
v___x_1582_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1574_, v_f_1573_, v_node_1581_, v_acc_1576_);
return v___x_1582_;
}
default: 
{
lean_object* v___x_1583_; 
lean_dec_ref(v_inst_1574_);
lean_dec(v_f_1573_);
v___x_1583_ = lean_apply_2(v_toPure_1575_, lean_box(0), v_acc_1576_);
return v___x_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux(lean_object* v_m_1584_, lean_object* v_inst_1585_, lean_object* v_00_u03c3_1586_, lean_object* v_00_u03b1_1587_, lean_object* v_00_u03b2_1588_, lean_object* v_f_1589_, lean_object* v_x_1590_, lean_object* v_x_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1585_, v_f_1589_, v_x_1590_, v_x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___redArg(lean_object* v_inst_1593_, lean_object* v_map_1594_, lean_object* v_f_1595_, lean_object* v_init_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1593_, v_f_1595_, v_map_1594_, v_init_1596_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM(lean_object* v_m_1598_, lean_object* v_inst_1599_, lean_object* v_00_u03c3_1600_, lean_object* v_00_u03b1_1601_, lean_object* v_00_u03b2_1602_, lean_object* v_x_1603_, lean_object* v_x_1604_, lean_object* v_map_1605_, lean_object* v_f_1606_, lean_object* v_init_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1599_, v_f_1606_, v_map_1605_, v_init_1607_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___boxed(lean_object* v_m_1609_, lean_object* v_inst_1610_, lean_object* v_00_u03c3_1611_, lean_object* v_00_u03b1_1612_, lean_object* v_00_u03b2_1613_, lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v_map_1616_, lean_object* v_f_1617_, lean_object* v_init_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Lean_PersistentHashMap_foldlM(v_m_1609_, v_inst_1610_, v_00_u03c3_1611_, v_00_u03b1_1612_, v_00_u03b2_1613_, v_x_1614_, v_x_1615_, v_map_1616_, v_f_1617_, v_init_1618_);
lean_dec_ref(v_x_1615_);
lean_dec_ref(v_x_1614_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg___lam__0(lean_object* v_f_1620_, lean_object* v_x_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = lean_apply_2(v_f_1620_, v___y_1622_, v___y_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg(lean_object* v_inst_1625_, lean_object* v_map_1626_, lean_object* v_f_1627_){
_start:
{
lean_object* v___f_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___f_1628_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1628_, 0, v_f_1627_);
v___x_1629_ = lean_box(0);
v___x_1630_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1625_, v___f_1628_, v_map_1626_, v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM(lean_object* v_m_1631_, lean_object* v_inst_1632_, lean_object* v_00_u03b1_1633_, lean_object* v_00_u03b2_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_, lean_object* v_map_1637_, lean_object* v_f_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_1632_, v_map_1637_, v_f_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___boxed(lean_object* v_m_1640_, lean_object* v_inst_1641_, lean_object* v_00_u03b1_1642_, lean_object* v_00_u03b2_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_, lean_object* v_map_1646_, lean_object* v_f_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_PersistentHashMap_forM(v_m_1640_, v_inst_1641_, v_00_u03b1_1642_, v_00_u03b2_1643_, v_x_1644_, v_x_1645_, v_map_1646_, v_f_1647_);
lean_dec_ref(v_x_1645_);
lean_dec_ref(v_x_1644_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg___lam__0(lean_object* v_f_1649_, lean_object* v_x1_1650_, lean_object* v_x2_1651_, lean_object* v_x3_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_apply_3(v_f_1649_, v_x1_1650_, v_x2_1651_, v_x3_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object* v_map_1673_, lean_object* v_f_1674_, lean_object* v_init_1675_){
_start:
{
lean_object* v___f_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___f_1676_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1676_, 0, v_f_1674_);
v___x_1677_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1678_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1677_, v___f_1676_, v_map_1673_, v_init_1675_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl(lean_object* v_00_u03c3_1679_, lean_object* v_00_u03b1_1680_, lean_object* v_00_u03b2_1681_, lean_object* v_x_1682_, lean_object* v_x_1683_, lean_object* v_map_1684_, lean_object* v_f_1685_, lean_object* v_init_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_1684_, v_f_1685_, v_init_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___boxed(lean_object* v_00_u03c3_1688_, lean_object* v_00_u03b1_1689_, lean_object* v_00_u03b2_1690_, lean_object* v_x_1691_, lean_object* v_x_1692_, lean_object* v_map_1693_, lean_object* v_f_1694_, lean_object* v_init_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_PersistentHashMap_foldl(v_00_u03c3_1688_, v_00_u03b1_1689_, v_00_u03b2_1690_, v_x_1691_, v_x_1692_, v_map_1693_, v_f_1694_, v_init_1695_);
lean_dec_ref(v_x_1692_);
lean_dec_ref(v_x_1691_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit___redArg(lean_object* v_x_1697_, lean_object* v_x_1698_, lean_object* v_f_1699_, lean_object* v_old_1700_, lean_object* v_acc_1701_, lean_object* v_k_1702_, lean_object* v_v_1703_){
_start:
{
uint8_t v___x_1704_; 
lean_inc(v_k_1702_);
v___x_1704_ = l_Lean_PersistentHashMap_contains___redArg(v_x_1697_, v_x_1698_, v_old_1700_, v_k_1702_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_apply_3(v_f_1699_, v_acc_1701_, v_k_1702_, v_v_1703_);
return v___x_1705_;
}
else
{
lean_dec(v_v_1703_);
lean_dec(v_k_1702_);
lean_dec(v_f_1699_);
return v_acc_1701_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit(lean_object* v_00_u03c3_1706_, lean_object* v_00_u03b1_1707_, lean_object* v_00_u03b2_1708_, lean_object* v_x_1709_, lean_object* v_x_1710_, lean_object* v_f_1711_, lean_object* v_old_1712_, lean_object* v_acc_1713_, lean_object* v_k_1714_, lean_object* v_v_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit___redArg(v_x_1709_, v_x_1710_, v_f_1711_, v_old_1712_, v_acc_1713_, v_k_1714_, v_v_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg(lean_object* v_x_1717_, lean_object* v_x_1718_, lean_object* v_f_1719_, lean_object* v_old_1720_, lean_object* v_ks_1721_, lean_object* v_vs_1722_, lean_object* v_i_1723_, lean_object* v_acc_1724_){
_start:
{
lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = lean_array_get_size(v_ks_1721_);
v___x_1726_ = lean_nat_dec_lt(v_i_1723_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_dec(v_i_1723_);
lean_dec_ref(v_old_1720_);
lean_dec(v_f_1719_);
lean_dec_ref(v_x_1718_);
lean_dec_ref(v_x_1717_);
return v_acc_1724_;
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1727_ = lean_unsigned_to_nat(1u);
v___x_1728_ = lean_nat_add(v_i_1723_, v___x_1727_);
v___x_1729_ = lean_array_fget_borrowed(v_ks_1721_, v_i_1723_);
v___x_1730_ = lean_array_fget_borrowed(v_vs_1722_, v_i_1723_);
lean_dec(v_i_1723_);
lean_inc(v___x_1730_);
lean_inc(v___x_1729_);
lean_inc_ref(v_old_1720_);
lean_inc(v_f_1719_);
lean_inc_ref(v_x_1718_);
lean_inc_ref(v_x_1717_);
v___x_1731_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit___redArg(v_x_1717_, v_x_1718_, v_f_1719_, v_old_1720_, v_acc_1724_, v___x_1729_, v___x_1730_);
v_i_1723_ = v___x_1728_;
v_acc_1724_ = v___x_1731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg___boxed(lean_object* v_x_1733_, lean_object* v_x_1734_, lean_object* v_f_1735_, lean_object* v_old_1736_, lean_object* v_ks_1737_, lean_object* v_vs_1738_, lean_object* v_i_1739_, lean_object* v_acc_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg(v_x_1733_, v_x_1734_, v_f_1735_, v_old_1736_, v_ks_1737_, v_vs_1738_, v_i_1739_, v_acc_1740_);
lean_dec_ref(v_vs_1738_);
lean_dec_ref(v_ks_1737_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision(lean_object* v_00_u03c3_1742_, lean_object* v_00_u03b1_1743_, lean_object* v_00_u03b2_1744_, lean_object* v_x_1745_, lean_object* v_x_1746_, lean_object* v_f_1747_, lean_object* v_old_1748_, lean_object* v_ks_1749_, lean_object* v_vs_1750_, lean_object* v_h_1751_, lean_object* v_i_1752_, lean_object* v_acc_1753_){
_start:
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg(v_x_1745_, v_x_1746_, v_f_1747_, v_old_1748_, v_ks_1749_, v_vs_1750_, v_i_1752_, v_acc_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___boxed(lean_object* v_00_u03c3_1755_, lean_object* v_00_u03b1_1756_, lean_object* v_00_u03b2_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_, lean_object* v_f_1760_, lean_object* v_old_1761_, lean_object* v_ks_1762_, lean_object* v_vs_1763_, lean_object* v_h_1764_, lean_object* v_i_1765_, lean_object* v_acc_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision(v_00_u03c3_1755_, v_00_u03b1_1756_, v_00_u03b2_1757_, v_x_1758_, v_x_1759_, v_f_1760_, v_old_1761_, v_ks_1762_, v_vs_1763_, v_h_1764_, v_i_1765_, v_acc_1766_);
lean_dec_ref(v_vs_1763_);
lean_dec_ref(v_ks_1762_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(lean_object* v_x_1768_, lean_object* v_x_1769_, lean_object* v_f_1770_, lean_object* v_old_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
if (lean_obj_tag(v_a_1772_) == 0)
{
lean_object* v_es_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v_es_1774_ = lean_ctor_get(v_a_1772_, 0);
lean_inc_ref(v_es_1774_);
lean_dec_ref_known(v_a_1772_, 1);
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = lean_array_get_size(v_es_1774_);
v___x_1777_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1778_ = lean_nat_dec_lt(v___x_1775_, v___x_1776_);
if (v___x_1778_ == 0)
{
lean_dec_ref(v_es_1774_);
lean_dec_ref(v_old_1771_);
lean_dec(v_f_1770_);
lean_dec_ref(v_x_1769_);
lean_dec_ref(v_x_1768_);
return v_a_1773_;
}
else
{
lean_object* v___f_1779_; uint8_t v___x_1780_; 
v___f_1779_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg___lam__0), 6, 4);
lean_closure_set(v___f_1779_, 0, v_x_1768_);
lean_closure_set(v___f_1779_, 1, v_x_1769_);
lean_closure_set(v___f_1779_, 2, v_f_1770_);
lean_closure_set(v___f_1779_, 3, v_old_1771_);
v___x_1780_ = lean_nat_dec_le(v___x_1776_, v___x_1776_);
if (v___x_1780_ == 0)
{
if (v___x_1778_ == 0)
{
lean_dec_ref(v___f_1779_);
lean_dec_ref(v_es_1774_);
return v_a_1773_;
}
else
{
size_t v___x_1781_; size_t v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = ((size_t)0ULL);
v___x_1782_ = lean_usize_of_nat(v___x_1776_);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1777_, v___f_1779_, v_es_1774_, v___x_1781_, v___x_1782_, v_a_1773_);
return v___x_1783_;
}
}
else
{
size_t v___x_1784_; size_t v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = ((size_t)0ULL);
v___x_1785_ = lean_usize_of_nat(v___x_1776_);
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1777_, v___f_1779_, v_es_1774_, v___x_1784_, v___x_1785_, v_a_1773_);
return v___x_1786_;
}
}
}
else
{
lean_object* v_ks_1787_; lean_object* v_vs_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_ks_1787_ = lean_ctor_get(v_a_1772_, 0);
lean_inc_ref(v_ks_1787_);
v_vs_1788_ = lean_ctor_get(v_a_1772_, 1);
lean_inc_ref(v_vs_1788_);
lean_dec_ref_known(v_a_1772_, 2);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg(v_x_1768_, v_x_1769_, v_f_1770_, v_old_1771_, v_ks_1787_, v_vs_1788_, v___x_1789_, v_a_1773_);
lean_dec_ref(v_vs_1788_);
lean_dec_ref(v_ks_1787_);
return v___x_1790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg___lam__0(lean_object* v_x_1791_, lean_object* v_x_1792_, lean_object* v_f_1793_, lean_object* v_old_1794_, lean_object* v_x1_1795_, lean_object* v_x2_1796_){
_start:
{
switch(lean_obj_tag(v_x2_1796_))
{
case 0:
{
lean_object* v_key_1797_; lean_object* v_val_1798_; lean_object* v___x_1799_; 
v_key_1797_ = lean_ctor_get(v_x2_1796_, 0);
lean_inc(v_key_1797_);
v_val_1798_ = lean_ctor_get(v_x2_1796_, 1);
lean_inc(v_val_1798_);
lean_dec_ref_known(v_x2_1796_, 2);
v___x_1799_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit___redArg(v_x_1791_, v_x_1792_, v_f_1793_, v_old_1794_, v_x1_1795_, v_key_1797_, v_val_1798_);
return v___x_1799_;
}
case 1:
{
lean_object* v_node_1800_; lean_object* v___x_1801_; 
v_node_1800_ = lean_ctor_get(v_x2_1796_, 0);
lean_inc(v_node_1800_);
lean_dec_ref_known(v_x2_1796_, 1);
v___x_1801_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(v_x_1791_, v_x_1792_, v_f_1793_, v_old_1794_, v_node_1800_, v_x1_1795_);
return v___x_1801_;
}
default: 
{
lean_dec_ref(v_old_1794_);
lean_dec(v_f_1793_);
lean_dec_ref(v_x_1792_);
lean_dec_ref(v_x_1791_);
return v_x1_1795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll(lean_object* v_00_u03c3_1802_, lean_object* v_00_u03b1_1803_, lean_object* v_00_u03b2_1804_, lean_object* v_x_1805_, lean_object* v_x_1806_, lean_object* v_f_1807_, lean_object* v_old_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(v_x_1805_, v_x_1806_, v_f_1807_, v_old_1808_, v_a_1809_, v_a_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg(lean_object* v_x_1812_, lean_object* v_x_1813_, lean_object* v_f_1814_, lean_object* v_old_1815_, lean_object* v_nes_1816_, lean_object* v_oes_1817_, lean_object* v_i_1818_, lean_object* v_acc_1819_){
_start:
{
lean_object* v___y_1821_; lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = lean_array_get_size(v_nes_1816_);
v___x_1826_ = lean_nat_dec_lt(v_i_1818_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_dec(v_i_1818_);
lean_dec_ref(v_old_1815_);
lean_dec(v_f_1814_);
lean_dec_ref(v_x_1813_);
lean_dec_ref(v_x_1812_);
return v_acc_1819_;
}
else
{
lean_object* v_ne_1827_; lean_object* v___y_1829_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v_ne_1827_ = lean_array_fget_borrowed(v_nes_1816_, v_i_1818_);
v___x_1841_ = lean_array_get_size(v_oes_1817_);
v___x_1842_ = lean_nat_dec_lt(v_i_1818_, v___x_1841_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_box(2);
v___y_1829_ = v___x_1843_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_array_fget_borrowed(v_oes_1817_, v_i_1818_);
v___y_1829_ = v___x_1844_;
goto v___jp_1828_;
}
v___jp_1828_:
{
size_t v___x_1830_; size_t v___x_1831_; uint8_t v___x_1832_; 
v___x_1830_ = lean_ptr_addr(v_ne_1827_);
v___x_1831_ = lean_ptr_addr(v___y_1829_);
v___x_1832_ = lean_usize_dec_eq(v___x_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
switch(lean_obj_tag(v_ne_1827_))
{
case 0:
{
lean_object* v_key_1833_; lean_object* v_val_1834_; lean_object* v___x_1835_; 
v_key_1833_ = lean_ctor_get(v_ne_1827_, 0);
v_val_1834_ = lean_ctor_get(v_ne_1827_, 1);
lean_inc(v_val_1834_);
lean_inc(v_key_1833_);
lean_inc_ref(v_old_1815_);
lean_inc(v_f_1814_);
lean_inc_ref(v_x_1813_);
lean_inc_ref(v_x_1812_);
v___x_1835_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit___redArg(v_x_1812_, v_x_1813_, v_f_1814_, v_old_1815_, v_acc_1819_, v_key_1833_, v_val_1834_);
v___y_1821_ = v___x_1835_;
goto v___jp_1820_;
}
case 1:
{
if (lean_obj_tag(v___y_1829_) == 1)
{
lean_object* v_node_1836_; lean_object* v_node_1837_; lean_object* v___x_1838_; 
v_node_1836_ = lean_ctor_get(v_ne_1827_, 0);
v_node_1837_ = lean_ctor_get(v___y_1829_, 0);
lean_inc(v_node_1836_);
lean_inc_ref(v_old_1815_);
lean_inc(v_f_1814_);
lean_inc_ref(v_x_1813_);
lean_inc_ref(v_x_1812_);
v___x_1838_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(v_x_1812_, v_x_1813_, v_f_1814_, v_old_1815_, v_node_1836_, v_node_1837_, v_acc_1819_);
v___y_1821_ = v___x_1838_;
goto v___jp_1820_;
}
else
{
lean_object* v_node_1839_; lean_object* v___x_1840_; 
v_node_1839_ = lean_ctor_get(v_ne_1827_, 0);
lean_inc(v_node_1839_);
lean_inc_ref(v_old_1815_);
lean_inc(v_f_1814_);
lean_inc_ref(v_x_1813_);
lean_inc_ref(v_x_1812_);
v___x_1840_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(v_x_1812_, v_x_1813_, v_f_1814_, v_old_1815_, v_node_1839_, v_acc_1819_);
v___y_1821_ = v___x_1840_;
goto v___jp_1820_;
}
}
default: 
{
v___y_1821_ = v_acc_1819_;
goto v___jp_1820_;
}
}
}
else
{
v___y_1821_ = v_acc_1819_;
goto v___jp_1820_;
}
}
}
v___jp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1822_ = lean_unsigned_to_nat(1u);
v___x_1823_ = lean_nat_add(v_i_1818_, v___x_1822_);
lean_dec(v_i_1818_);
v_i_1818_ = v___x_1823_;
v_acc_1819_ = v___y_1821_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(lean_object* v_x_1845_, lean_object* v_x_1846_, lean_object* v_f_1847_, lean_object* v_old_1848_, lean_object* v_new_1849_, lean_object* v_old_1850_, lean_object* v_acc_1851_){
_start:
{
size_t v___x_1852_; size_t v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = lean_ptr_addr(v_new_1849_);
v___x_1853_ = lean_ptr_addr(v_old_1850_);
v___x_1854_ = lean_usize_dec_eq(v___x_1852_, v___x_1853_);
if (v___x_1854_ == 0)
{
if (lean_obj_tag(v_new_1849_) == 0)
{
if (lean_obj_tag(v_old_1850_) == 0)
{
lean_object* v_es_1855_; lean_object* v_es_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v_es_1855_ = lean_ctor_get(v_new_1849_, 0);
lean_inc_ref(v_es_1855_);
lean_dec_ref_known(v_new_1849_, 1);
v_es_1856_ = lean_ctor_get(v_old_1850_, 0);
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg(v_x_1845_, v_x_1846_, v_f_1847_, v_old_1848_, v_es_1855_, v_es_1856_, v___x_1857_, v_acc_1851_);
lean_dec_ref(v_es_1855_);
return v___x_1858_;
}
else
{
lean_object* v___x_1859_; 
v___x_1859_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(v_x_1845_, v_x_1846_, v_f_1847_, v_old_1848_, v_new_1849_, v_acc_1851_);
return v___x_1859_;
}
}
else
{
lean_object* v___x_1860_; 
v___x_1860_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(v_x_1845_, v_x_1846_, v_f_1847_, v_old_1848_, v_new_1849_, v_acc_1851_);
return v___x_1860_;
}
}
else
{
lean_dec_ref(v_new_1849_);
lean_dec_ref(v_old_1848_);
lean_dec(v_f_1847_);
lean_dec_ref(v_x_1846_);
lean_dec_ref(v_x_1845_);
return v_acc_1851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg___boxed(lean_object* v_x_1861_, lean_object* v_x_1862_, lean_object* v_f_1863_, lean_object* v_old_1864_, lean_object* v_new_1865_, lean_object* v_old_1866_, lean_object* v_acc_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(v_x_1861_, v_x_1862_, v_f_1863_, v_old_1864_, v_new_1865_, v_old_1866_, v_acc_1867_);
lean_dec_ref(v_old_1866_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg___boxed(lean_object* v_x_1869_, lean_object* v_x_1870_, lean_object* v_f_1871_, lean_object* v_old_1872_, lean_object* v_nes_1873_, lean_object* v_oes_1874_, lean_object* v_i_1875_, lean_object* v_acc_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg(v_x_1869_, v_x_1870_, v_f_1871_, v_old_1872_, v_nes_1873_, v_oes_1874_, v_i_1875_, v_acc_1876_);
lean_dec_ref(v_oes_1874_);
lean_dec_ref(v_nes_1873_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries(lean_object* v_00_u03c3_1878_, lean_object* v_00_u03b1_1879_, lean_object* v_00_u03b2_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_, lean_object* v_f_1883_, lean_object* v_old_1884_, lean_object* v_nes_1885_, lean_object* v_oes_1886_, lean_object* v_i_1887_, lean_object* v_acc_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg(v_x_1881_, v_x_1882_, v_f_1883_, v_old_1884_, v_nes_1885_, v_oes_1886_, v_i_1887_, v_acc_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___boxed(lean_object* v_00_u03c3_1890_, lean_object* v_00_u03b1_1891_, lean_object* v_00_u03b2_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_f_1895_, lean_object* v_old_1896_, lean_object* v_nes_1897_, lean_object* v_oes_1898_, lean_object* v_i_1899_, lean_object* v_acc_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries(v_00_u03c3_1890_, v_00_u03b1_1891_, v_00_u03b2_1892_, v_x_1893_, v_x_1894_, v_f_1895_, v_old_1896_, v_nes_1897_, v_oes_1898_, v_i_1899_, v_acc_1900_);
lean_dec_ref(v_oes_1898_);
lean_dec_ref(v_nes_1897_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go(lean_object* v_00_u03c3_1902_, lean_object* v_00_u03b1_1903_, lean_object* v_00_u03b2_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_, lean_object* v_f_1907_, lean_object* v_old_1908_, lean_object* v_new_1909_, lean_object* v_old_1910_, lean_object* v_acc_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(v_x_1905_, v_x_1906_, v_f_1907_, v_old_1908_, v_new_1909_, v_old_1910_, v_acc_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___boxed(lean_object* v_00_u03c3_1913_, lean_object* v_00_u03b1_1914_, lean_object* v_00_u03b2_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_, lean_object* v_f_1918_, lean_object* v_old_1919_, lean_object* v_new_1920_, lean_object* v_old_1921_, lean_object* v_acc_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go(v_00_u03c3_1913_, v_00_u03b1_1914_, v_00_u03b2_1915_, v_x_1916_, v_x_1917_, v_f_1918_, v_old_1919_, v_new_1920_, v_old_1921_, v_acc_1922_);
lean_dec_ref(v_old_1921_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe___redArg(lean_object* v_x_1924_, lean_object* v_x_1925_, lean_object* v_f_1926_, lean_object* v_new_1927_, lean_object* v_old_1928_, lean_object* v_init_1929_){
_start:
{
lean_object* v___x_1930_; 
lean_inc_ref(v_old_1928_);
v___x_1930_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(v_x_1924_, v_x_1925_, v_f_1926_, v_old_1928_, v_new_1927_, v_old_1928_, v_init_1929_);
lean_dec_ref(v_old_1928_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe(lean_object* v_00_u03c3_1931_, lean_object* v_00_u03b1_1932_, lean_object* v_00_u03b2_1933_, lean_object* v_x_1934_, lean_object* v_x_1935_, lean_object* v_f_1936_, lean_object* v_new_1937_, lean_object* v_old_1938_, lean_object* v_init_1939_){
_start:
{
lean_object* v___x_1940_; 
lean_inc_ref(v_old_1938_);
v___x_1940_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(v_x_1934_, v_x_1935_, v_f_1936_, v_old_1938_, v_new_1937_, v_old_1938_, v_init_1939_);
lean_dec_ref(v_old_1938_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__0(lean_object* v_x_1941_){
_start:
{
if (lean_obj_tag(v_x_1941_) == 0)
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
v_a_1942_ = lean_ctor_get(v_x_1941_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_x_1941_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v_x_1941_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v_x_1941_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
else
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
v_a_1950_ = lean_ctor_get(v_x_1941_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_x_1941_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v_x_1941_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v_x_1941_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__1(lean_object* v_toPure_1958_, lean_object* v_result_1959_){
_start:
{
lean_object* v_a_1960_; lean_object* v___x_1961_; 
v_a_1960_ = lean_ctor_get(v_result_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref(v_result_1959_);
v___x_1961_ = lean_apply_2(v_toPure_1958_, lean_box(0), v_a_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__2(lean_object* v_toFunctor_1962_, lean_object* v_f_1963_, lean_object* v_intoError_1964_, lean_object* v_s_1965_, lean_object* v_a_1966_, lean_object* v_b_1967_){
_start:
{
lean_object* v_map_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1977_; 
v_map_1968_ = lean_ctor_get(v_toFunctor_1962_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_toFunctor_1962_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; 
v_unused_1978_ = lean_ctor_get(v_toFunctor_1962_, 1);
lean_dec(v_unused_1978_);
v___x_1970_ = v_toFunctor_1962_;
v_isShared_1971_ = v_isSharedCheck_1977_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_map_1968_);
lean_dec(v_toFunctor_1962_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1977_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 1, v_b_1967_);
lean_ctor_set(v___x_1970_, 0, v_a_1966_);
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1966_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v_b_1967_);
v___x_1973_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1974_ = lean_apply_2(v_f_1963_, v___x_1973_, v_s_1965_);
v___x_1975_ = lean_apply_4(v_map_1968_, lean_box(0), lean_box(0), v_intoError_1964_, v___x_1974_);
return v___x_1975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg(lean_object* v_inst_1980_, lean_object* v_map_1981_, lean_object* v_init_1982_, lean_object* v_f_1983_){
_start:
{
lean_object* v_toApplicative_1984_; lean_object* v_toBind_1985_; lean_object* v___f_1986_; lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___f_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v_toFunctor_1996_; lean_object* v_toPure_1997_; lean_object* v_intoError_1998_; lean_object* v___f_1999_; lean_object* v___f_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v_toApplicative_1984_ = lean_ctor_get(v_inst_1980_, 0);
lean_inc_ref(v_toApplicative_1984_);
v_toBind_1985_ = lean_ctor_get(v_inst_1980_, 1);
lean_inc(v_toBind_1985_);
lean_inc_ref_n(v_inst_1980_, 6);
v___f_1986_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1986_, 0, v_inst_1980_);
v___f_1987_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1987_, 0, v_inst_1980_);
v___f_1988_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1988_, 0, v_inst_1980_);
v___f_1989_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1989_, 0, v_inst_1980_);
v___x_1990_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1990_, 0, lean_box(0));
lean_closure_set(v___x_1990_, 1, lean_box(0));
lean_closure_set(v___x_1990_, 2, v_inst_1980_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v___f_1986_);
v___x_1992_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1992_, 0, lean_box(0));
lean_closure_set(v___x_1992_, 1, lean_box(0));
lean_closure_set(v___x_1992_, 2, v_inst_1980_);
v___x_1993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
lean_ctor_set(v___x_1993_, 2, v___f_1987_);
lean_ctor_set(v___x_1993_, 3, v___f_1988_);
lean_ctor_set(v___x_1993_, 4, v___f_1989_);
v___x_1994_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1994_, 0, lean_box(0));
lean_closure_set(v___x_1994_, 1, lean_box(0));
lean_closure_set(v___x_1994_, 2, v_inst_1980_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v_toFunctor_1996_ = lean_ctor_get(v_toApplicative_1984_, 0);
lean_inc_ref(v_toFunctor_1996_);
v_toPure_1997_ = lean_ctor_get(v_toApplicative_1984_, 1);
lean_inc(v_toPure_1997_);
lean_dec_ref(v_toApplicative_1984_);
v_intoError_1998_ = ((lean_object*)(l_Lean_PersistentHashMap_forIn___redArg___closed__0));
v___f_1999_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1999_, 0, v_toPure_1997_);
v___f_2000_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__2), 6, 3);
lean_closure_set(v___f_2000_, 0, v_toFunctor_1996_);
lean_closure_set(v___f_2000_, 1, v_f_1983_);
lean_closure_set(v___f_2000_, 2, v_intoError_1998_);
lean_inc_ref(v_map_1981_);
v___x_2001_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1995_, v___f_2000_, v_map_1981_, v_init_1982_);
v___x_2002_ = lean_apply_4(v_toBind_1985_, lean_box(0), lean_box(0), v___x_2001_, v___f_1999_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___boxed(lean_object* v_inst_2003_, lean_object* v_map_2004_, lean_object* v_init_2005_, lean_object* v_f_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_2003_, v_map_2004_, v_init_2005_, v_f_2006_);
lean_dec_ref(v_map_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn(lean_object* v_m_2008_, lean_object* v_00_u03c3_2009_, lean_object* v_00_u03b1_2010_, lean_object* v_00_u03b2_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_, lean_object* v_inst_2014_, lean_object* v_map_2015_, lean_object* v_init_2016_, lean_object* v_f_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_2014_, v_map_2015_, v_init_2016_, v_f_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___boxed(lean_object* v_m_2019_, lean_object* v_00_u03c3_2020_, lean_object* v_00_u03b1_2021_, lean_object* v_00_u03b2_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_, lean_object* v_inst_2025_, lean_object* v_map_2026_, lean_object* v_init_2027_, lean_object* v_f_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_PersistentHashMap_forIn(v_m_2019_, v_00_u03c3_2020_, v_00_u03b1_2021_, v_00_u03b2_2022_, v_x_2023_, v_x_2024_, v_inst_2025_, v_map_2026_, v_init_2027_, v_f_2028_);
lean_dec_ref(v_map_2026_);
lean_dec_ref(v_x_2024_);
lean_dec_ref(v_x_2023_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_inst_2030_, lean_object* v_00_u03b2_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_2030_, v___y_2032_, v___y_2033_, v___y_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed(lean_object* v_inst_2036_, lean_object* v_00_u03b2_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(v_inst_2036_, v_00_u03b2_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec_ref(v___y_2038_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg(lean_object* v_inst_2042_){
_start:
{
lean_object* v___f_2043_; 
v___f_2043_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2043_, 0, v_inst_2042_);
return v___f_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad(lean_object* v_m_2044_, lean_object* v_00_u03b1_2045_, lean_object* v_00_u03b2_2046_, lean_object* v_x_2047_, lean_object* v_x_2048_, lean_object* v_inst_2049_){
_start:
{
lean_object* v___f_2050_; 
v___f_2050_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2050_, 0, v_inst_2049_);
return v___f_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___boxed(lean_object* v_m_2051_, lean_object* v_00_u03b1_2052_, lean_object* v_00_u03b2_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v_inst_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_PersistentHashMap_instForInProdOfMonad(v_m_2051_, v_00_u03b1_2052_, v_00_u03b2_2053_, v_x_2054_, v_x_2055_, v_inst_2056_);
lean_dec_ref(v_x_2055_);
lean_dec_ref(v_x_2054_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__0(lean_object* v_toPure_2058_, lean_object* v_entries_x27_2059_){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2060_, 0, v_entries_x27_2059_);
v___x_2061_ = lean_apply_2(v_toPure_2058_, lean_box(0), v___x_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__1(lean_object* v_toPure_2062_, lean_object* v_____do__lift_2063_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_____do__lift_2063_);
v___x_2065_ = lean_apply_2(v_toPure_2062_, lean_box(0), v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__2(lean_object* v_key_2066_, lean_object* v_toPure_2067_, lean_object* v_____do__lift_2068_){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_key_2066_);
lean_ctor_set(v___x_2069_, 1, v_____do__lift_2068_);
v___x_2070_ = lean_apply_2(v_toPure_2067_, lean_box(0), v___x_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__4(lean_object* v_ks_2071_, lean_object* v_toPure_2072_, lean_object* v_____x_2073_){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_ks_2071_);
lean_ctor_set(v___x_2074_, 1, v_____x_2073_);
v___x_2075_ = lean_apply_2(v_toPure_2072_, lean_box(0), v___x_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg(lean_object* v_inst_2076_, lean_object* v_f_2077_, lean_object* v_n_2078_){
_start:
{
if (lean_obj_tag(v_n_2078_) == 0)
{
lean_object* v_toApplicative_2079_; lean_object* v_toBind_2080_; lean_object* v_toPure_2081_; lean_object* v_es_2082_; lean_object* v___f_2083_; lean_object* v___f_2084_; lean_object* v___f_2085_; size_t v_sz_2086_; size_t v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_toApplicative_2079_ = lean_ctor_get(v_inst_2076_, 0);
v_toBind_2080_ = lean_ctor_get(v_inst_2076_, 1);
lean_inc_n(v_toBind_2080_, 2);
v_toPure_2081_ = lean_ctor_get(v_toApplicative_2079_, 1);
v_es_2082_ = lean_ctor_get(v_n_2078_, 0);
lean_inc_ref(v_es_2082_);
lean_dec_ref_known(v_n_2078_, 1);
lean_inc_n(v_toPure_2081_, 3);
v___f_2083_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2083_, 0, v_toPure_2081_);
v___f_2084_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2084_, 0, v_toPure_2081_);
lean_inc_ref(v_inst_2076_);
v___f_2085_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2085_, 0, v_toPure_2081_);
lean_closure_set(v___f_2085_, 1, v_f_2077_);
lean_closure_set(v___f_2085_, 2, v_toBind_2080_);
lean_closure_set(v___f_2085_, 3, v_inst_2076_);
lean_closure_set(v___f_2085_, 4, v___f_2084_);
v_sz_2086_ = lean_array_size(v_es_2082_);
v___x_2087_ = ((size_t)0ULL);
v___x_2088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2076_, v___f_2085_, v_sz_2086_, v___x_2087_, v_es_2082_);
v___x_2089_ = lean_apply_4(v_toBind_2080_, lean_box(0), lean_box(0), v___x_2088_, v___f_2083_);
return v___x_2089_;
}
else
{
lean_object* v_toApplicative_2090_; lean_object* v_toBind_2091_; lean_object* v_toPure_2092_; lean_object* v_ks_2093_; lean_object* v_vs_2094_; lean_object* v___f_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v_toApplicative_2090_ = lean_ctor_get(v_inst_2076_, 0);
v_toBind_2091_ = lean_ctor_get(v_inst_2076_, 1);
lean_inc(v_toBind_2091_);
v_toPure_2092_ = lean_ctor_get(v_toApplicative_2090_, 1);
v_ks_2093_ = lean_ctor_get(v_n_2078_, 0);
lean_inc_ref(v_ks_2093_);
v_vs_2094_ = lean_ctor_get(v_n_2078_, 1);
lean_inc_ref(v_vs_2094_);
lean_dec_ref_known(v_n_2078_, 2);
lean_inc(v_toPure_2092_);
v___f_2095_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__4), 3, 2);
lean_closure_set(v___f_2095_, 0, v_ks_2093_);
lean_closure_set(v___f_2095_, 1, v_toPure_2092_);
v___x_2096_ = l_Array_mapM_x27___redArg(v_inst_2076_, v_f_2077_, v_vs_2094_);
v___x_2097_ = lean_apply_4(v_toBind_2091_, lean_box(0), lean_box(0), v___x_2096_, v___f_2095_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__3(lean_object* v_toPure_2098_, lean_object* v_f_2099_, lean_object* v_toBind_2100_, lean_object* v_inst_2101_, lean_object* v___f_2102_, lean_object* v_x_2103_){
_start:
{
switch(lean_obj_tag(v_x_2103_))
{
case 0:
{
lean_object* v_key_2104_; lean_object* v_val_2105_; lean_object* v___f_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec(v___f_2102_);
lean_dec_ref(v_inst_2101_);
v_key_2104_ = lean_ctor_get(v_x_2103_, 0);
lean_inc(v_key_2104_);
v_val_2105_ = lean_ctor_get(v_x_2103_, 1);
lean_inc(v_val_2105_);
lean_dec_ref_known(v_x_2103_, 2);
v___f_2106_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2106_, 0, v_key_2104_);
lean_closure_set(v___f_2106_, 1, v_toPure_2098_);
v___x_2107_ = lean_apply_1(v_f_2099_, v_val_2105_);
v___x_2108_ = lean_apply_4(v_toBind_2100_, lean_box(0), lean_box(0), v___x_2107_, v___f_2106_);
return v___x_2108_;
}
case 1:
{
lean_object* v_node_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_dec(v_toPure_2098_);
v_node_2109_ = lean_ctor_get(v_x_2103_, 0);
lean_inc(v_node_2109_);
lean_dec_ref_known(v_x_2103_, 1);
v___x_2110_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_2101_, v_f_2099_, v_node_2109_);
v___x_2111_ = lean_apply_4(v_toBind_2100_, lean_box(0), lean_box(0), v___x_2110_, v___f_2102_);
return v___x_2111_;
}
default: 
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v___f_2102_);
lean_dec_ref(v_inst_2101_);
lean_dec(v_toBind_2100_);
lean_dec(v_f_2099_);
v___x_2112_ = lean_box(2);
v___x_2113_ = lean_apply_2(v_toPure_2098_, lean_box(0), v___x_2112_);
return v___x_2113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux(lean_object* v_00_u03b1_2114_, lean_object* v_00_u03b2_2115_, lean_object* v_00_u03c3_2116_, lean_object* v_m_2117_, lean_object* v_inst_2118_, lean_object* v_f_2119_, lean_object* v_n_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_2118_, v_f_2119_, v_n_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg___lam__0(lean_object* v_toPure_2122_, lean_object* v_root_2123_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_apply_2(v_toPure_2122_, lean_box(0), v_root_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object* v_inst_2125_, lean_object* v_pm_2126_, lean_object* v_f_2127_){
_start:
{
lean_object* v_toApplicative_2128_; lean_object* v_toBind_2129_; lean_object* v_toPure_2130_; lean_object* v___x_2131_; lean_object* v___f_2132_; lean_object* v___x_2133_; 
v_toApplicative_2128_ = lean_ctor_get(v_inst_2125_, 0);
v_toBind_2129_ = lean_ctor_get(v_inst_2125_, 1);
lean_inc(v_toBind_2129_);
v_toPure_2130_ = lean_ctor_get(v_toApplicative_2128_, 1);
lean_inc(v_toPure_2130_);
v___x_2131_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_2125_, v_f_2127_, v_pm_2126_);
v___f_2132_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2132_, 0, v_toPure_2130_);
v___x_2133_ = lean_apply_4(v_toBind_2129_, lean_box(0), lean_box(0), v___x_2131_, v___f_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM(lean_object* v_00_u03b1_2134_, lean_object* v_00_u03b2_2135_, lean_object* v_00_u03c3_2136_, lean_object* v_m_2137_, lean_object* v_inst_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_, lean_object* v_pm_2141_, lean_object* v_f_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_2138_, v_pm_2141_, v_f_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___boxed(lean_object* v_00_u03b1_2144_, lean_object* v_00_u03b2_2145_, lean_object* v_00_u03c3_2146_, lean_object* v_m_2147_, lean_object* v_inst_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_, lean_object* v_pm_2151_, lean_object* v_f_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Lean_PersistentHashMap_mapM(v_00_u03b1_2144_, v_00_u03b2_2145_, v_00_u03c3_2146_, v_m_2147_, v_inst_2148_, v_x_2149_, v_x_2150_, v_pm_2151_, v_f_2152_);
lean_dec_ref(v_x_2150_);
lean_dec_ref(v_x_2149_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg___lam__0(lean_object* v_f_2154_, lean_object* v_x_2155_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_apply_1(v_f_2154_, v_x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg(lean_object* v_pm_2157_, lean_object* v_f_2158_){
_start:
{
lean_object* v___f_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___f_2159_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2159_, 0, v_f_2158_);
v___x_2160_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_2161_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_2160_, v_pm_2157_, v___f_2159_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map(lean_object* v_00_u03b1_2162_, lean_object* v_00_u03b2_2163_, lean_object* v_00_u03c3_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_, lean_object* v_pm_2167_, lean_object* v_f_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_PersistentHashMap_map___redArg(v_pm_2167_, v_f_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___boxed(lean_object* v_00_u03b1_2170_, lean_object* v_00_u03b2_2171_, lean_object* v_00_u03c3_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_, lean_object* v_pm_2175_, lean_object* v_f_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_PersistentHashMap_map(v_00_u03b1_2170_, v_00_u03b2_2171_, v_00_u03c3_2172_, v_x_2173_, v_x_2174_, v_pm_2175_, v_f_2176_);
lean_dec_ref(v_x_2174_);
lean_dec_ref(v_x_2173_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg___lam__0(lean_object* v_ps_2178_, lean_object* v_k_2179_, lean_object* v_v_2180_){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2181_, 0, v_k_2179_);
lean_ctor_set(v___x_2181_, 1, v_v_2180_);
v___x_2182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v_ps_2178_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg(lean_object* v_m_2184_){
_start:
{
lean_object* v___f_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___f_2185_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___redArg___closed__0));
v___x_2186_ = lean_box(0);
v___x_2187_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_2184_, v___f_2185_, v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList(lean_object* v_00_u03b1_2188_, lean_object* v_00_u03b2_2189_, lean_object* v_x_2190_, lean_object* v_x_2191_, lean_object* v_m_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_PersistentHashMap_toList___redArg(v_m_2192_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___boxed(lean_object* v_00_u03b1_2194_, lean_object* v_00_u03b2_2195_, lean_object* v_x_2196_, lean_object* v_x_2197_, lean_object* v_m_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_PersistentHashMap_toList(v_00_u03b1_2194_, v_00_u03b2_2195_, v_x_2196_, v_x_2197_, v_m_2198_);
lean_dec_ref(v_x_2197_);
lean_dec_ref(v_x_2196_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg___lam__0(lean_object* v_ps_2200_, lean_object* v_k_2201_, lean_object* v_v_2202_){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_k_2201_);
lean_ctor_set(v___x_2203_, 1, v_v_2202_);
v___x_2204_ = lean_array_push(v_ps_2200_, v___x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg(lean_object* v_m_2208_){
_start:
{
lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___f_2209_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__0));
v___x_2210_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__1));
v___x_2211_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_2208_, v___f_2209_, v___x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray(lean_object* v_00_u03b1_2212_, lean_object* v_00_u03b2_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_, lean_object* v_m_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_PersistentHashMap_toArray___redArg(v_m_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___boxed(lean_object* v_00_u03b1_2218_, lean_object* v_00_u03b2_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_, lean_object* v_m_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_PersistentHashMap_toArray(v_00_u03b1_2218_, v_00_u03b2_2219_, v_x_2220_, v_x_2221_, v_m_2222_);
lean_dec_ref(v_x_2221_);
lean_dec_ref(v_x_2220_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg(lean_object* v_x_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_){
_start:
{
if (lean_obj_tag(v_x_2224_) == 0)
{
lean_object* v_es_2227_; lean_object* v_numNodes_2228_; lean_object* v_numNull_2229_; lean_object* v_numCollisions_2230_; lean_object* v_maxDepth_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2253_; 
v_es_2227_ = lean_ctor_get(v_x_2224_, 0);
v_numNodes_2228_ = lean_ctor_get(v_x_2225_, 0);
v_numNull_2229_ = lean_ctor_get(v_x_2225_, 1);
v_numCollisions_2230_ = lean_ctor_get(v_x_2225_, 2);
v_maxDepth_2231_ = lean_ctor_get(v_x_2225_, 3);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_x_2225_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2233_ = v_x_2225_;
v_isShared_2234_ = v_isSharedCheck_2253_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_maxDepth_2231_);
lean_inc(v_numCollisions_2230_);
lean_inc(v_numNull_2229_);
lean_inc(v_numNodes_2228_);
lean_dec(v_x_2225_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2253_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___y_2238_; uint8_t v___x_2252_; 
v___x_2235_ = lean_unsigned_to_nat(1u);
v___x_2236_ = lean_nat_add(v_numNodes_2228_, v___x_2235_);
lean_dec(v_numNodes_2228_);
v___x_2252_ = lean_nat_dec_le(v_maxDepth_2231_, v_x_2226_);
if (v___x_2252_ == 0)
{
v___y_2238_ = v_maxDepth_2231_;
goto v___jp_2237_;
}
else
{
lean_dec(v_maxDepth_2231_);
lean_inc(v_x_2226_);
v___y_2238_ = v_x_2226_;
goto v___jp_2237_;
}
v___jp_2237_:
{
lean_object* v_stats_2240_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 3, v___y_2238_);
lean_ctor_set(v___x_2233_, 0, v___x_2236_);
v_stats_2240_ = v___x_2233_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_numNull_2229_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v_numCollisions_2230_);
lean_ctor_set(v_reuseFailAlloc_2251_, 3, v___y_2238_);
v_stats_2240_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = lean_array_get_size(v_es_2227_);
v___x_2243_ = lean_nat_dec_lt(v___x_2241_, v___x_2242_);
if (v___x_2243_ == 0)
{
lean_dec(v_x_2226_);
return v_stats_2240_;
}
else
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_nat_dec_le(v___x_2242_, v___x_2242_);
if (v___x_2244_ == 0)
{
if (v___x_2243_ == 0)
{
lean_dec(v_x_2226_);
return v_stats_2240_;
}
else
{
size_t v___x_2245_; size_t v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = ((size_t)0ULL);
v___x_2246_ = lean_usize_of_nat(v___x_2242_);
v___x_2247_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2226_, v_es_2227_, v___x_2245_, v___x_2246_, v_stats_2240_);
lean_dec(v_x_2226_);
return v___x_2247_;
}
}
else
{
size_t v___x_2248_; size_t v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = lean_usize_of_nat(v___x_2242_);
v___x_2250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2226_, v_es_2227_, v___x_2248_, v___x_2249_, v_stats_2240_);
lean_dec(v_x_2226_);
return v___x_2250_;
}
}
}
}
}
}
else
{
lean_object* v_ks_2254_; lean_object* v_numNodes_2255_; lean_object* v_numNull_2256_; lean_object* v_numCollisions_2257_; lean_object* v_maxDepth_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2274_; 
v_ks_2254_ = lean_ctor_get(v_x_2224_, 0);
v_numNodes_2255_ = lean_ctor_get(v_x_2225_, 0);
v_numNull_2256_ = lean_ctor_get(v_x_2225_, 1);
v_numCollisions_2257_ = lean_ctor_get(v_x_2225_, 2);
v_maxDepth_2258_ = lean_ctor_get(v_x_2225_, 3);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_x_2225_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2260_ = v_x_2225_;
v_isShared_2261_ = v_isSharedCheck_2274_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_maxDepth_2258_);
lean_inc(v_numCollisions_2257_);
lean_inc(v_numNull_2256_);
lean_inc(v_numNodes_2255_);
lean_dec(v_x_2225_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2274_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v___x_2262_ = lean_unsigned_to_nat(1u);
v___x_2263_ = lean_nat_add(v_numNodes_2255_, v___x_2262_);
lean_dec(v_numNodes_2255_);
v___x_2264_ = lean_array_get_size(v_ks_2254_);
v___x_2265_ = lean_nat_add(v_numCollisions_2257_, v___x_2264_);
lean_dec(v_numCollisions_2257_);
v___x_2266_ = lean_nat_sub(v___x_2265_, v___x_2262_);
lean_dec(v___x_2265_);
v___x_2267_ = lean_nat_dec_le(v_maxDepth_2258_, v_x_2226_);
if (v___x_2267_ == 0)
{
lean_object* v___x_2269_; 
lean_dec(v_x_2226_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 2, v___x_2266_);
lean_ctor_set(v___x_2260_, 0, v___x_2263_);
v___x_2269_ = v___x_2260_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_numNull_2256_);
lean_ctor_set(v_reuseFailAlloc_2270_, 2, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2270_, 3, v_maxDepth_2258_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
else
{
lean_object* v___x_2272_; 
lean_dec(v_maxDepth_2258_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 3, v_x_2226_);
lean_ctor_set(v___x_2260_, 2, v___x_2266_);
lean_ctor_set(v___x_2260_, 0, v___x_2263_);
v___x_2272_ = v___x_2260_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_numNull_2256_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v___x_2266_);
lean_ctor_set(v_reuseFailAlloc_2273_, 3, v_x_2226_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(lean_object* v_x_2275_, lean_object* v_as_2276_, size_t v_i_2277_, size_t v_stop_2278_, lean_object* v_b_2279_){
_start:
{
lean_object* v___y_2281_; uint8_t v___x_2285_; 
v___x_2285_ = lean_usize_dec_eq(v_i_2277_, v_stop_2278_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_unsigned_to_nat(1u);
v___x_2287_ = lean_array_uget_borrowed(v_as_2276_, v_i_2277_);
switch(lean_obj_tag(v___x_2287_))
{
case 0:
{
v___y_2281_ = v_b_2279_;
goto v___jp_2280_;
}
case 1:
{
lean_object* v_node_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_node_2288_ = lean_ctor_get(v___x_2287_, 0);
v___x_2289_ = lean_nat_add(v_x_2275_, v___x_2286_);
v___x_2290_ = l_Lean_PersistentHashMap_collectStats___redArg(v_node_2288_, v_b_2279_, v___x_2289_);
v___y_2281_ = v___x_2290_;
goto v___jp_2280_;
}
default: 
{
lean_object* v_numNodes_2291_; lean_object* v_numNull_2292_; lean_object* v_numCollisions_2293_; lean_object* v_maxDepth_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_numNodes_2291_ = lean_ctor_get(v_b_2279_, 0);
v_numNull_2292_ = lean_ctor_get(v_b_2279_, 1);
v_numCollisions_2293_ = lean_ctor_get(v_b_2279_, 2);
v_maxDepth_2294_ = lean_ctor_get(v_b_2279_, 3);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_b_2279_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2296_ = v_b_2279_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_maxDepth_2294_);
lean_inc(v_numCollisions_2293_);
lean_inc(v_numNull_2292_);
lean_inc(v_numNodes_2291_);
lean_dec(v_b_2279_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = lean_nat_add(v_numNull_2292_, v___x_2286_);
lean_dec(v_numNull_2292_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 1, v___x_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_numNodes_2291_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2301_, 2, v_numCollisions_2293_);
lean_ctor_set(v_reuseFailAlloc_2301_, 3, v_maxDepth_2294_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
v___y_2281_ = v___x_2300_;
goto v___jp_2280_;
}
}
}
}
}
else
{
return v_b_2279_;
}
v___jp_2280_:
{
size_t v___x_2282_; size_t v___x_2283_; 
v___x_2282_ = ((size_t)1ULL);
v___x_2283_ = lean_usize_add(v_i_2277_, v___x_2282_);
v_i_2277_ = v___x_2283_;
v_b_2279_ = v___y_2281_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2275_ = stack[0].m_obj;
lean_object* v_as_2276_ = stack[1].m_obj;
size_t v_i_2277_ = stack[2].m_num;
size_t v_stop_2278_ = stack[3].m_num;
lean_object* v_b_2279_ = stack[4].m_obj;
lean_object* v_res_2303_;
v_res_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2275_, v_as_2276_, v_i_2277_, v_stop_2278_, v_b_2279_);
stack->m_obj
 = v_res_2303_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg___boxed(lean_object* v_x_2304_, lean_object* v_as_2305_, lean_object* v_i_2306_, lean_object* v_stop_2307_, lean_object* v_b_2308_){
_start:
{
size_t v_i_boxed_2309_; size_t v_stop_boxed_2310_; lean_object* v_res_2311_; 
v_i_boxed_2309_ = lean_unbox_usize(v_i_2306_);
lean_dec(v_i_2306_);
v_stop_boxed_2310_ = lean_unbox_usize(v_stop_2307_);
lean_dec(v_stop_2307_);
v_res_2311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2304_, v_as_2305_, v_i_boxed_2309_, v_stop_boxed_2310_, v_b_2308_);
lean_dec_ref(v_as_2305_);
lean_dec(v_x_2304_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg___boxed(lean_object* v_x_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2312_, v_x_2313_, v_x_2314_);
lean_dec_ref(v_x_2312_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats(lean_object* v_00_u03b1_2316_, lean_object* v_00_u03b2_2317_, lean_object* v_x_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2318_, v_x_2319_, v_x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___boxed(lean_object* v_00_u03b1_2322_, lean_object* v_00_u03b2_2323_, lean_object* v_x_2324_, lean_object* v_x_2325_, lean_object* v_x_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_PersistentHashMap_collectStats(v_00_u03b1_2322_, v_00_u03b2_2323_, v_x_2324_, v_x_2325_, v_x_2326_);
lean_dec_ref(v_x_2324_);
return v_res_2327_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(lean_object* v_00_u03b1_2328_, lean_object* v_00_u03b2_2329_, lean_object* v_x_2330_, lean_object* v_as_2331_, size_t v_i_2332_, size_t v_stop_2333_, lean_object* v_b_2334_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2330_, v_as_2331_, v_i_2332_, v_stop_2333_, v_b_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2330_ = stack[2].m_obj;
lean_object* v_as_2331_ = stack[3].m_obj;
size_t v_i_2332_ = stack[4].m_num;
size_t v_stop_2333_ = stack[5].m_num;
lean_object* v_b_2334_ = stack[6].m_obj;
lean_object* v_res_2336_;
v_res_2336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(lean_box(0), lean_box(0), v_x_2330_, v_as_2331_, v_i_2332_, v_stop_2333_, v_b_2334_);
stack->m_obj
 = v_res_2336_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2337_, lean_object* v_00_u03b2_2338_, lean_object* v_x_2339_, lean_object* v_as_2340_, lean_object* v_i_2341_, lean_object* v_stop_2342_, lean_object* v_b_2343_){
_start:
{
size_t v_i_boxed_2344_; size_t v_stop_boxed_2345_; lean_object* v_res_2346_; 
v_i_boxed_2344_ = lean_unbox_usize(v_i_2341_);
lean_dec(v_i_2341_);
v_stop_boxed_2345_ = lean_unbox_usize(v_stop_2342_);
lean_dec(v_stop_2342_);
v_res_2346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(v_00_u03b1_2337_, v_00_u03b2_2338_, v_x_2339_, v_as_2340_, v_i_boxed_2344_, v_stop_boxed_2345_, v_b_2343_);
lean_dec_ref(v_as_2340_);
lean_dec(v_x_2339_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg(lean_object* v_m_2349_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = ((lean_object*)(l_Lean_PersistentHashMap_stats___redArg___closed__0));
v___x_2351_ = lean_unsigned_to_nat(1u);
v___x_2352_ = l_Lean_PersistentHashMap_collectStats___redArg(v_m_2349_, v___x_2350_, v___x_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg___boxed(lean_object* v_m_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2353_);
lean_dec_ref(v_m_2353_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats(lean_object* v_00_u03b1_2355_, lean_object* v_00_u03b2_2356_, lean_object* v_x_2357_, lean_object* v_x_2358_, lean_object* v_m_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___boxed(lean_object* v_00_u03b1_2361_, lean_object* v_00_u03b2_2362_, lean_object* v_x_2363_, lean_object* v_x_2364_, lean_object* v_m_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_PersistentHashMap_stats(v_00_u03b1_2361_, v_00_u03b2_2362_, v_x_2363_, v_x_2364_, v_m_2365_);
lean_dec_ref(v_m_2365_);
lean_dec_ref(v_x_2364_);
lean_dec_ref(v_x_2363_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Stats_toString(lean_object* v_s_2372_){
_start:
{
lean_object* v_numNodes_2373_; lean_object* v_numNull_2374_; lean_object* v_numCollisions_2375_; lean_object* v_maxDepth_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_numNodes_2373_ = lean_ctor_get(v_s_2372_, 0);
lean_inc(v_numNodes_2373_);
v_numNull_2374_ = lean_ctor_get(v_s_2372_, 1);
lean_inc(v_numNull_2374_);
v_numCollisions_2375_ = lean_ctor_get(v_s_2372_, 2);
lean_inc(v_numCollisions_2375_);
v_maxDepth_2376_ = lean_ctor_get(v_s_2372_, 3);
lean_inc(v_maxDepth_2376_);
lean_dec_ref(v_s_2372_);
v___x_2377_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__0));
v___x_2378_ = l_Nat_reprFast(v_numNodes_2373_);
v___x_2379_ = lean_string_append(v___x_2377_, v___x_2378_);
lean_dec_ref(v___x_2378_);
v___x_2380_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__1));
v___x_2381_ = lean_string_append(v___x_2379_, v___x_2380_);
v___x_2382_ = l_Nat_reprFast(v_numNull_2374_);
v___x_2383_ = lean_string_append(v___x_2381_, v___x_2382_);
lean_dec_ref(v___x_2382_);
v___x_2384_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__2));
v___x_2385_ = lean_string_append(v___x_2383_, v___x_2384_);
v___x_2386_ = l_Nat_reprFast(v_numCollisions_2375_);
v___x_2387_ = lean_string_append(v___x_2385_, v___x_2386_);
lean_dec_ref(v___x_2386_);
v___x_2388_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__3));
v___x_2389_ = lean_string_append(v___x_2387_, v___x_2388_);
v___x_2390_ = l_Nat_reprFast(v_maxDepth_2376_);
v___x_2391_ = lean_string_append(v___x_2389_, v___x_2390_);
lean_dec_ref(v___x_2390_);
v___x_2392_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__4));
v___x_2393_ = lean_string_append(v___x_2391_, v___x_2392_);
return v___x_2393_;
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
