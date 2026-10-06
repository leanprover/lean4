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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry___redArg(){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(2);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry___redArg___boxed(lean_object* v___dummy_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_PersistentHashMap_instInhabitedEntry___redArg();
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object* v_00_u03b1_77_, lean_object* v_00_u03b2_78_, lean_object* v_00_u03c3_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_box(2);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl___redArg(lean_object* v_x_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_tag_nat(v_x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl___redArg___boxed(lean_object* v_x_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_PersistentHashMap_Node_ctorIdx___impl___redArg(v_x_83_);
lean_dec_ref(v_x_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_x_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = lean_obj_tag_nat(v_x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorIdx___impl___boxed(lean_object* v_00_u03b1_89_, lean_object* v_00_u03b2_90_, lean_object* v_x_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_PersistentHashMap_Node_ctorIdx___impl(v_00_u03b1_89_, v_00_u03b2_90_, v_x_91_);
lean_dec_ref(v_x_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim___redArg(lean_object* v_t_93_, lean_object* v_k_94_){
_start:
{
if (lean_obj_tag(v_t_93_) == 0)
{
lean_object* v_es_95_; lean_object* v___x_96_; 
v_es_95_ = lean_ctor_get(v_t_93_, 0);
lean_inc_ref(v_es_95_);
lean_dec_ref_known(v_t_93_, 1);
v___x_96_ = lean_apply_1(v_k_94_, v_es_95_);
return v___x_96_;
}
else
{
lean_object* v_ks_97_; lean_object* v_vs_98_; lean_object* v___x_99_; 
v_ks_97_ = lean_ctor_get(v_t_93_, 0);
lean_inc_ref(v_ks_97_);
v_vs_98_ = lean_ctor_get(v_t_93_, 1);
lean_inc_ref(v_vs_98_);
lean_dec_ref_known(v_t_93_, 2);
v___x_99_ = lean_apply_3(v_k_94_, v_ks_97_, v_vs_98_, lean_box(0));
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim(lean_object* v_00_u03b1_100_, lean_object* v_00_u03b2_101_, lean_object* v_motive__1_102_, lean_object* v_ctorIdx_103_, lean_object* v_t_104_, lean_object* v_h_105_, lean_object* v_k_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_104_, v_k_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_ctorElim___boxed(lean_object* v_00_u03b1_108_, lean_object* v_00_u03b2_109_, lean_object* v_motive__1_110_, lean_object* v_ctorIdx_111_, lean_object* v_t_112_, lean_object* v_h_113_, lean_object* v_k_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_PersistentHashMap_Node_ctorElim(v_00_u03b1_108_, v_00_u03b2_109_, v_motive__1_110_, v_ctorIdx_111_, v_t_112_, v_h_113_, v_k_114_);
lean_dec(v_ctorIdx_111_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_entries_elim___redArg(lean_object* v_t_116_, lean_object* v_entries_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_116_, v_entries_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_entries_elim(lean_object* v_00_u03b1_119_, lean_object* v_00_u03b2_120_, lean_object* v_motive__1_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_entries_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_122_, v_entries_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_collision_elim___redArg(lean_object* v_t_126_, lean_object* v_collision_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_126_, v_collision_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_collision_elim(lean_object* v_00_u03b1_129_, lean_object* v_00_u03b2_130_, lean_object* v_motive__1_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_collision_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_Lean_PersistentHashMap_Node_ctorElim___redArg(v_t_132_, v_collision_134_);
return v___x_135_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
lean_object* v_es_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v_es_137_ = lean_ctor_get(v_x_136_, 0);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_array_get_size(v_es_137_);
v___x_140_ = lean_nat_dec_lt(v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
uint8_t v___x_141_; 
v___x_141_ = 1;
return v___x_141_;
}
else
{
if (v___x_140_ == 0)
{
return v___x_140_;
}
else
{
size_t v___x_142_; size_t v___x_143_; uint8_t v___x_144_; 
v___x_142_ = ((size_t)0ULL);
v___x_143_ = lean_usize_of_nat(v___x_139_);
v___x_144_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_es_137_, v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
return v___x_140_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
}
}
else
{
uint8_t v___x_146_; 
v___x_146_ = 0;
return v___x_146_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(lean_object* v_as_147_, size_t v_i_148_, size_t v_stop_149_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = lean_usize_dec_eq(v_i_148_, v_stop_149_);
if (v___x_154_ == 0)
{
uint8_t v___x_155_; lean_object* v___x_156_; 
v___x_155_ = 1;
v___x_156_ = lean_array_uget_borrowed(v_as_147_, v_i_148_);
switch(lean_obj_tag(v___x_156_))
{
case 0:
{
return v___x_155_;
}
case 1:
{
lean_object* v_node_157_; uint8_t v___x_158_; 
v_node_157_ = lean_ctor_get(v___x_156_, 0);
v___x_158_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_node_157_);
if (v___x_158_ == 0)
{
return v___x_155_;
}
else
{
goto v___jp_150_;
}
}
default: 
{
goto v___jp_150_;
}
}
}
else
{
uint8_t v___x_159_; 
v___x_159_ = 0;
return v___x_159_;
}
v___jp_150_:
{
size_t v___x_151_; size_t v___x_152_; 
v___x_151_ = ((size_t)1ULL);
v___x_152_ = lean_usize_add(v_i_148_, v___x_151_);
v_i_148_ = v___x_152_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg___boxed(lean_object* v_as_160_, lean_object* v_i_161_, lean_object* v_stop_162_){
_start:
{
size_t v_i_boxed_163_; size_t v_stop_boxed_164_; uint8_t v_res_165_; lean_object* v_r_166_; 
v_i_boxed_163_ = lean_unbox_usize(v_i_161_);
lean_dec(v_i_161_);
v_stop_boxed_164_ = lean_unbox_usize(v_stop_162_);
lean_dec(v_stop_162_);
v_res_165_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentHashMap_Node_isEmpty_spec__0___redArg(v_as_160_, v_i_boxed_163_, v_stop_boxed_164_);
lean_dec_ref(v_as_160_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Node_isEmpty___redArg___boxed(lean_object* v_x_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_167_);
lean_dec_ref(v_x_167_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode___redArg(){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = ((lean_object*)(l_Lean_PersistentHashMap_instInhabitedNode___redArg___closed__1));
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode___redArg___boxed(lean_object* v___dummy_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_PersistentHashMap_instInhabitedNode___redArg();
return v_res_201_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_instInhabitedNode___closed__0(void){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_PersistentHashMap_instInhabitedNode___redArg();
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabitedNode(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_obj_once(&l_Lean_PersistentHashMap_instInhabitedNode___closed__0, &l_Lean_PersistentHashMap_instInhabitedNode___closed__0_once, _init_l_Lean_PersistentHashMap_instInhabitedNode___closed__0);
return v___x_205_;
}
}
static size_t _init_l_Lean_PersistentHashMap_shift(void){
_start:
{
size_t v___x_206_; 
v___x_206_ = ((size_t)5ULL);
return v___x_206_;
}
}
static size_t _init_l_Lean_PersistentHashMap_branching(void){
_start:
{
size_t v___x_207_; 
v___x_207_ = ((size_t)32ULL);
return v___x_207_;
}
}
static size_t _init_l_Lean_PersistentHashMap_maxDepth(void){
_start:
{
size_t v___x_208_; 
v___x_208_ = ((size_t)7ULL);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_maxCollisions(void){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = lean_unsigned_to_nat(4u);
return v___x_209_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = lean_box(2);
v___x_211_ = lean_unsigned_to_nat(32u);
v___x_212_ = lean_mk_array(v___x_211_, v___x_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg(){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___closed__0);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg___boxed(lean_object* v___dummy_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v_res_216_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0(void){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object* v_00_u03b1_218_, lean_object* v_00_u03b2_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntriesArray___closed__0);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___redArg(){
_start:
{
lean_object* v___x_224_; 
v___x_224_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___redArg___closed__0, &l_Lean_PersistentHashMap_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___redArg___closed__0);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___redArg___boxed(lean_object* v___dummy_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_PersistentHashMap_empty___redArg();
return v_res_226_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___closed__0(void){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty(lean_object* v_00_u03b1_228_, lean_object* v_00_u03b2_229_, lean_object* v_inst_230_, lean_object* v_inst_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___closed__0, &l_Lean_PersistentHashMap_empty___closed__0_once, _init_l_Lean_PersistentHashMap_empty___closed__0);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___boxed(lean_object* v_00_u03b1_233_, lean_object* v_00_u03b2_234_, lean_object* v_inst_235_, lean_object* v_inst_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_PersistentHashMap_empty(v_00_u03b1_233_, v_00_u03b2_234_, v_inst_235_, v_inst_236_);
lean_dec_ref(v_inst_236_);
lean_dec_ref(v_inst_235_);
return v_res_237_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty___redArg(lean_object* v_x_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___redArg___boxed(lean_object* v_x_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Lean_PersistentHashMap_isEmpty___redArg(v_x_240_);
lean_dec_ref(v_x_240_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_isEmpty(lean_object* v_00_u03b1_243_, lean_object* v_00_u03b2_244_, lean_object* v_x_245_, lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
uint8_t v___x_248_; 
v___x_248_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isEmpty___boxed(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Lean_PersistentHashMap_isEmpty(v_00_u03b1_249_, v_00_u03b2_250_, v_x_251_, v_x_252_, v_x_253_);
lean_dec_ref(v_x_253_);
lean_dec_ref(v_x_252_);
lean_dec_ref(v_x_251_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___redArg___closed__0, &l_Lean_PersistentHashMap_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___redArg___closed__0);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___redArg___boxed(lean_object* v___dummy_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v_res_259_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_PersistentHashMap_instInhabited___redArg();
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_inst_263_, lean_object* v_inst_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = lean_obj_once(&l_Lean_PersistentHashMap_instInhabited___closed__0, &l_Lean_PersistentHashMap_instInhabited___closed__0_once, _init_l_Lean_PersistentHashMap_instInhabited___closed__0);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instInhabited___boxed(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_inst_268_, lean_object* v_inst_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_PersistentHashMap_instInhabited(v_00_u03b1_266_, v_00_u03b2_267_, v_inst_268_, v_inst_269_);
lean_dec_ref(v_inst_269_);
lean_dec_ref(v_inst_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg(){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___redArg___closed__0, &l_Lean_PersistentHashMap_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___redArg___closed__0);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg___boxed(lean_object* v___dummy_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v_res_274_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_mkEmptyEntries___closed__0(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object* v_00_u03b1_276_, lean_object* v_00_u03b2_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntries___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntries___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntries___closed__0);
return v___x_278_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_mul2Shift(size_t v_i_279_, size_t v_shift_280_){
_start:
{
size_t v___x_281_; 
v___x_281_ = lean_usize_shift_left(v_i_279_, v_shift_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mul2Shift___boxed(lean_object* v_i_282_, lean_object* v_shift_283_){
_start:
{
size_t v_i_boxed_284_; size_t v_shift_boxed_285_; size_t v_res_286_; lean_object* v_r_287_; 
v_i_boxed_284_ = lean_unbox_usize(v_i_282_);
lean_dec(v_i_282_);
v_shift_boxed_285_ = lean_unbox_usize(v_shift_283_);
lean_dec(v_shift_283_);
v_res_286_ = l_Lean_PersistentHashMap_mul2Shift(v_i_boxed_284_, v_shift_boxed_285_);
v_r_287_ = lean_box_usize(v_res_286_);
return v_r_287_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_div2Shift(size_t v_i_288_, size_t v_shift_289_){
_start:
{
size_t v___x_290_; 
v___x_290_ = lean_usize_shift_right(v_i_288_, v_shift_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_div2Shift___boxed(lean_object* v_i_291_, lean_object* v_shift_292_){
_start:
{
size_t v_i_boxed_293_; size_t v_shift_boxed_294_; size_t v_res_295_; lean_object* v_r_296_; 
v_i_boxed_293_ = lean_unbox_usize(v_i_291_);
lean_dec(v_i_291_);
v_shift_boxed_294_ = lean_unbox_usize(v_shift_292_);
lean_dec(v_shift_292_);
v_res_295_ = l_Lean_PersistentHashMap_div2Shift(v_i_boxed_293_, v_shift_boxed_294_);
v_r_296_ = lean_box_usize(v_res_295_);
return v_r_296_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentHashMap_mod2Shift(size_t v_i_297_, size_t v_shift_298_){
_start:
{
size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; 
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_shift_left(v___x_299_, v_shift_298_);
v___x_301_ = lean_usize_sub(v___x_300_, v___x_299_);
v___x_302_ = lean_usize_land(v_i_297_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mod2Shift___boxed(lean_object* v_i_303_, lean_object* v_shift_304_){
_start:
{
size_t v_i_boxed_305_; size_t v_shift_boxed_306_; size_t v_res_307_; lean_object* v_r_308_; 
v_i_boxed_305_ = lean_unbox_usize(v_i_303_);
lean_dec(v_i_303_);
v_shift_boxed_306_ = lean_unbox_usize(v_shift_304_);
lean_dec(v_shift_304_);
v_res_307_ = l_Lean_PersistentHashMap_mod2Shift(v_i_boxed_305_, v_shift_boxed_306_);
v_r_308_ = lean_box_usize(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(lean_object* v_inst_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
lean_object* v_ks_314_; lean_object* v_vs_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_340_; 
v_ks_314_ = lean_ctor_get(v_x_310_, 0);
v_vs_315_ = lean_ctor_get(v_x_310_, 1);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_310_);
if (v_isSharedCheck_340_ == 0)
{
v___x_317_ = v_x_310_;
v_isShared_318_ = v_isSharedCheck_340_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_vs_315_);
lean_inc(v_ks_314_);
lean_dec(v_x_310_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_340_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = lean_array_get_size(v_ks_314_);
v___x_320_ = lean_nat_dec_lt(v_x_311_, v___x_319_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
lean_dec(v_x_311_);
lean_dec_ref(v_inst_309_);
v___x_321_ = lean_array_push(v_ks_314_, v_x_312_);
v___x_322_ = lean_array_push(v_vs_315_, v_x_313_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 1, v___x_322_);
lean_ctor_set(v___x_317_, 0, v___x_321_);
v___x_324_ = v___x_317_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
else
{
lean_object* v_k_x27_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_k_x27_326_ = lean_array_fget_borrowed(v_ks_314_, v_x_311_);
lean_inc_ref(v_inst_309_);
lean_inc(v_k_x27_326_);
lean_inc(v_x_312_);
v___x_327_ = lean_apply_2(v_inst_309_, v_x_312_, v_k_x27_326_);
v___x_328_ = lean_unbox(v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_330_; 
if (v_isShared_318_ == 0)
{
v___x_330_ = v___x_317_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_ks_314_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_vs_315_);
v___x_330_ = v_reuseFailAlloc_334_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_nat_add(v_x_311_, v___x_331_);
lean_dec(v_x_311_);
v_x_310_ = v___x_330_;
v_x_311_ = v___x_332_;
goto _start;
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_dec_ref(v_inst_309_);
v___x_335_ = lean_array_fset(v_ks_314_, v_x_311_, v_x_312_);
v___x_336_ = lean_array_fset(v_vs_315_, v_x_311_, v_x_313_);
lean_dec(v_x_311_);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 1, v___x_336_);
lean_ctor_set(v___x_317_, 0, v___x_335_);
v___x_338_ = v___x_317_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_335_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v___x_336_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux(lean_object* v_00_u03b1_341_, lean_object* v_00_u03b2_342_, lean_object* v_inst_343_, lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_x_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(v_inst_343_, v_x_344_, v_x_345_, v_x_346_, v_x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(lean_object* v_inst_349_, lean_object* v_n_350_, lean_object* v_k_351_, lean_object* v_v_352_){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___redArg(v_inst_349_, v_n_350_, v___x_353_, v_k_351_, v_v_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode(lean_object* v_00_u03b1_355_, lean_object* v_00_u03b2_356_, lean_object* v_inst_357_, lean_object* v_n_358_, lean_object* v_k_359_, lean_object* v_v_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(v_inst_357_, v_n_358_, v_k_359_, v_v_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object* v_x_362_){
_start:
{
lean_object* v_ks_363_; lean_object* v___x_364_; 
v_ks_363_ = lean_ctor_get(v_x_362_, 0);
v___x_364_ = lean_array_get_size(v_ks_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg___boxed(lean_object* v_x_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_365_);
lean_dec_ref(v_x_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize(lean_object* v_00_u03b1_367_, lean_object* v_00_u03b2_368_, lean_object* v_x_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___boxed(lean_object* v_00_u03b1_371_, lean_object* v_00_u03b2_372_, lean_object* v_x_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_PersistentHashMap_getCollisionNodeSize(v_00_u03b1_371_, v_00_u03b2_372_, v_x_373_);
lean_dec_ref(v_x_373_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object* v_k_u2081_375_, lean_object* v_v_u2081_376_, lean_object* v_k_u2082_377_, lean_object* v_v_u2082_378_){
_start:
{
lean_object* v___x_379_; lean_object* v_ks_380_; lean_object* v___x_381_; lean_object* v_ks_382_; lean_object* v___x_383_; lean_object* v_vs_384_; lean_object* v___x_385_; 
v___x_379_ = lean_unsigned_to_nat(4u);
v_ks_380_ = lean_mk_empty_array_with_capacity(v___x_379_);
lean_inc_ref(v_ks_380_);
v___x_381_ = lean_array_push(v_ks_380_, v_k_u2081_375_);
v_ks_382_ = lean_array_push(v___x_381_, v_k_u2082_377_);
v___x_383_ = lean_array_push(v_ks_380_, v_v_u2081_376_);
v_vs_384_ = lean_array_push(v___x_383_, v_v_u2082_378_);
v___x_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_385_, 0, v_ks_382_);
lean_ctor_set(v___x_385_, 1, v_vs_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mkCollisionNode(lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_k_u2081_388_, lean_object* v_v_u2081_389_, lean_object* v_k_u2082_390_, lean_object* v_v_u2082_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_k_u2081_388_, v_v_u2081_389_, v_k_u2082_390_, v_v_u2082_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg(lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_x_395_, size_t v_x_396_, size_t v_x_397_, lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
lean_object* v_es_400_; size_t v___x_401_; size_t v___x_402_; lean_object* v_j_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v_es_400_ = lean_ctor_get(v_x_395_, 0);
v___x_401_ = ((size_t)31ULL);
v___x_402_ = lean_usize_land(v_x_396_, v___x_401_);
v_j_403_ = lean_usize_to_nat(v___x_402_);
v___x_404_ = lean_array_get_size(v_es_400_);
v___x_405_ = lean_nat_dec_lt(v_j_403_, v___x_404_);
if (v___x_405_ == 0)
{
lean_dec(v_j_403_);
lean_dec(v_x_399_);
lean_dec(v_x_398_);
lean_dec_ref(v_inst_394_);
lean_dec_ref(v_inst_393_);
return v_x_395_;
}
else
{
lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_445_; 
lean_inc_ref(v_es_400_);
v_isSharedCheck_445_ = !lean_is_exclusive(v_x_395_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v_x_395_, 0);
lean_dec(v_unused_446_);
v___x_407_ = v_x_395_;
v_isShared_408_ = v_isSharedCheck_445_;
goto v_resetjp_406_;
}
else
{
lean_dec(v_x_395_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_445_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v_v_409_; lean_object* v___x_410_; lean_object* v_xs_x27_411_; lean_object* v___y_413_; 
v_v_409_ = lean_array_fget(v_es_400_, v_j_403_);
v___x_410_ = lean_box(0);
v_xs_x27_411_ = lean_array_fset(v_es_400_, v_j_403_, v___x_410_);
switch(lean_obj_tag(v_v_409_))
{
case 0:
{
lean_object* v_key_418_; lean_object* v_val_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_430_; 
lean_dec_ref(v_inst_394_);
v_key_418_ = lean_ctor_get(v_v_409_, 0);
v_val_419_ = lean_ctor_get(v_v_409_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v_v_409_);
if (v_isSharedCheck_430_ == 0)
{
v___x_421_ = v_v_409_;
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_val_419_);
lean_inc(v_key_418_);
lean_dec(v_v_409_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; uint8_t v___x_424_; 
lean_inc(v_key_418_);
lean_inc(v_x_398_);
v___x_423_ = lean_apply_2(v_inst_393_, v_x_398_, v_key_418_);
v___x_424_ = lean_unbox(v___x_423_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_del_object(v___x_421_);
v___x_425_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_418_, v_val_419_, v_x_398_, v_x_399_);
v___x_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
v___y_413_ = v___x_426_;
goto v___jp_412_;
}
else
{
lean_object* v___x_428_; 
lean_dec(v_val_419_);
lean_dec(v_key_418_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v_x_399_);
lean_ctor_set(v___x_421_, 0, v_x_398_);
v___x_428_ = v___x_421_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_x_398_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_x_399_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
v___y_413_ = v___x_428_;
goto v___jp_412_;
}
}
}
}
case 1:
{
lean_object* v_node_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_443_; 
v_node_431_ = lean_ctor_get(v_v_409_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v_v_409_);
if (v_isSharedCheck_443_ == 0)
{
v___x_433_ = v_v_409_;
v_isShared_434_ = v_isSharedCheck_443_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_node_431_);
lean_dec(v_v_409_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_443_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
size_t v___x_435_; size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; 
v___x_435_ = ((size_t)5ULL);
v___x_436_ = lean_usize_shift_right(v_x_396_, v___x_435_);
v___x_437_ = ((size_t)1ULL);
v___x_438_ = lean_usize_add(v_x_397_, v___x_437_);
v___x_439_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_393_, v_inst_394_, v_node_431_, v___x_436_, v___x_438_, v_x_398_, v_x_399_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_439_);
v___x_441_ = v___x_433_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v___x_439_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
v___y_413_ = v___x_441_;
goto v___jp_412_;
}
}
}
default: 
{
lean_object* v___x_444_; 
lean_dec_ref(v_inst_394_);
lean_dec_ref(v_inst_393_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_x_398_);
lean_ctor_set(v___x_444_, 1, v_x_399_);
v___y_413_ = v___x_444_;
goto v___jp_412_;
}
}
v___jp_412_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_array_fset(v_xs_x27_411_, v_j_403_, v___y_413_);
lean_dec(v_j_403_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_414_);
v___x_416_ = v___x_407_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
else
{
lean_object* v_ks_447_; lean_object* v_vs_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_466_; 
v_ks_447_ = lean_ctor_get(v_x_395_, 0);
v_vs_448_ = lean_ctor_get(v_x_395_, 1);
v_isSharedCheck_466_ = !lean_is_exclusive(v_x_395_);
if (v_isSharedCheck_466_ == 0)
{
v___x_450_ = v_x_395_;
v_isShared_451_ = v_isSharedCheck_466_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_vs_448_);
lean_inc(v_ks_447_);
lean_dec(v_x_395_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_466_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_ks_447_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_vs_448_);
v___x_453_ = v_reuseFailAlloc_465_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
lean_object* v_val_454_; size_t v___x_455_; uint8_t v___x_456_; 
lean_inc_ref(v_inst_393_);
v_val_454_ = l_Lean_PersistentHashMap_insertAtCollisionNode___redArg(v_inst_393_, v___x_453_, v_x_398_, v_x_399_);
v___x_455_ = ((size_t)7ULL);
v___x_456_ = lean_usize_dec_le(v___x_455_, v_x_397_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_457_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_val_454_);
v___x_458_ = lean_unsigned_to_nat(4u);
v___x_459_ = lean_nat_dec_lt(v___x_457_, v___x_458_);
lean_dec(v___x_457_);
if (v___x_459_ == 0)
{
lean_object* v_ks_460_; lean_object* v_vs_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_ks_460_ = lean_ctor_get(v_val_454_, 0);
lean_inc_ref(v_ks_460_);
v_vs_461_ = lean_ctor_get(v_val_454_, 1);
lean_inc_ref(v_vs_461_);
lean_dec_ref(v_val_454_);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_obj_once(&l_Lean_PersistentHashMap_mkEmptyEntries___closed__0, &l_Lean_PersistentHashMap_mkEmptyEntries___closed__0_once, _init_l_Lean_PersistentHashMap_mkEmptyEntries___closed__0);
v___x_464_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_393_, v_inst_394_, v_x_397_, v_ks_460_, v_vs_461_, v___x_462_, v___x_463_);
lean_dec_ref(v_vs_461_);
lean_dec_ref(v_ks_460_);
return v___x_464_;
}
else
{
lean_dec_ref(v_inst_394_);
lean_dec_ref(v_inst_393_);
return v_val_454_;
}
}
else
{
lean_dec_ref(v_inst_394_);
lean_dec_ref(v_inst_393_);
return v_val_454_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(lean_object* v_inst_467_, lean_object* v_inst_468_, size_t v_depth_469_, lean_object* v_keys_470_, lean_object* v_vals_471_, lean_object* v_i_472_, lean_object* v_entries_473_){
_start:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_array_get_size(v_keys_470_);
v___x_475_ = lean_nat_dec_lt(v_i_472_, v___x_474_);
if (v___x_475_ == 0)
{
lean_dec(v_i_472_);
lean_dec_ref(v_inst_468_);
lean_dec_ref(v_inst_467_);
return v_entries_473_;
}
else
{
lean_object* v_k_476_; lean_object* v_v_477_; lean_object* v___x_478_; uint64_t v___x_479_; size_t v_h_480_; size_t v___x_481_; lean_object* v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; size_t v_h_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_k_476_ = lean_array_fget_borrowed(v_keys_470_, v_i_472_);
v_v_477_ = lean_array_fget_borrowed(v_vals_471_, v_i_472_);
lean_inc_ref_n(v_inst_468_, 2);
lean_inc_n(v_k_476_, 2);
v___x_478_ = lean_apply_1(v_inst_468_, v_k_476_);
v___x_479_ = lean_unbox_uint64(v___x_478_);
lean_dec_ref(v___x_478_);
v_h_480_ = lean_uint64_to_usize(v___x_479_);
v___x_481_ = ((size_t)5ULL);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_sub(v_depth_469_, v___x_483_);
v___x_485_ = lean_usize_mul(v___x_481_, v___x_484_);
v_h_486_ = lean_usize_shift_right(v_h_480_, v___x_485_);
v___x_487_ = lean_nat_add(v_i_472_, v___x_482_);
lean_dec(v_i_472_);
lean_inc(v_v_477_);
lean_inc_ref(v_inst_467_);
v___x_488_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_467_, v_inst_468_, v_entries_473_, v_h_486_, v_depth_469_, v_k_476_, v_v_477_);
v_i_472_ = v___x_487_;
v_entries_473_ = v___x_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg___boxed(lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_depth_492_, lean_object* v_keys_493_, lean_object* v_vals_494_, lean_object* v_i_495_, lean_object* v_entries_496_){
_start:
{
size_t v_depth_boxed_497_; lean_object* v_res_498_; 
v_depth_boxed_497_ = lean_unbox_usize(v_depth_492_);
lean_dec(v_depth_492_);
v_res_498_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_490_, v_inst_491_, v_depth_boxed_497_, v_keys_493_, v_vals_494_, v_i_495_, v_entries_496_);
lean_dec_ref(v_vals_494_);
lean_dec_ref(v_keys_493_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___redArg___boxed(lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
size_t v_x_394__boxed_506_; size_t v_x_395__boxed_507_; lean_object* v_res_508_; 
v_x_394__boxed_506_ = lean_unbox_usize(v_x_502_);
lean_dec(v_x_502_);
v_x_395__boxed_507_ = lean_unbox_usize(v_x_503_);
lean_dec(v_x_503_);
v_res_508_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_499_, v_inst_500_, v_x_501_, v_x_394__boxed_506_, v_x_395__boxed_507_, v_x_504_, v_x_505_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(lean_object* v_00_u03b1_509_, lean_object* v_00_u03b2_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, size_t v_depth_513_, lean_object* v_keys_514_, lean_object* v_vals_515_, lean_object* v_heq_516_, lean_object* v_i_517_, lean_object* v_entries_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___redArg(v_inst_511_, v_inst_512_, v_depth_513_, v_keys_514_, v_vals_515_, v_i_517_, v_entries_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___boxed(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_depth_524_, lean_object* v_keys_525_, lean_object* v_vals_526_, lean_object* v_heq_527_, lean_object* v_i_528_, lean_object* v_entries_529_){
_start:
{
size_t v_depth_boxed_530_; lean_object* v_res_531_; 
v_depth_boxed_530_ = lean_unbox_usize(v_depth_524_);
lean_dec(v_depth_524_);
v_res_531_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse(v_00_u03b1_520_, v_00_u03b2_521_, v_inst_522_, v_inst_523_, v_depth_boxed_530_, v_keys_525_, v_vals_526_, v_heq_527_, v_i_528_, v_entries_529_);
lean_dec_ref(v_vals_526_);
lean_dec_ref(v_keys_525_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux(lean_object* v_00_u03b1_532_, lean_object* v_00_u03b2_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_x_536_, size_t v_x_537_, size_t v_x_538_, lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_534_, v_inst_535_, v_x_536_, v_x_537_, v_x_538_, v_x_539_, v_x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___boxed(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_, lean_object* v_inst_544_, lean_object* v_inst_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_, lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
size_t v_x_569__boxed_551_; size_t v_x_570__boxed_552_; lean_object* v_res_553_; 
v_x_569__boxed_551_ = lean_unbox_usize(v_x_547_);
lean_dec(v_x_547_);
v_x_570__boxed_552_ = lean_unbox_usize(v_x_548_);
lean_dec(v_x_548_);
v_res_553_ = l_Lean_PersistentHashMap_insertAux(v_00_u03b1_542_, v_00_u03b2_543_, v_inst_544_, v_inst_545_, v_x_546_, v_x_569__boxed_551_, v_x_570__boxed_552_, v_x_549_, v_x_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
lean_object* v___x_559_; uint64_t v___x_560_; size_t v___x_561_; size_t v___x_562_; lean_object* v___x_563_; 
lean_inc_ref(v_x_555_);
lean_inc(v_x_557_);
v___x_559_ = lean_apply_1(v_x_555_, v_x_557_);
v___x_560_ = lean_unbox_uint64(v___x_559_);
lean_dec_ref(v___x_559_);
v___x_561_ = lean_uint64_to_usize(v___x_560_);
v___x_562_ = ((size_t)1ULL);
v___x_563_ = l_Lean_PersistentHashMap_insertAux___redArg(v_x_554_, v_x_555_, v_x_556_, v___x_561_, v___x_562_, v_x_557_, v_x_558_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert(lean_object* v_00_u03b1_564_, lean_object* v_00_u03b2_565_, lean_object* v_x_566_, lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_PersistentHashMap_insert___redArg(v_x_566_, v_x_567_, v_x_568_, v_x_569_, v_x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg(lean_object* v_inst_572_, lean_object* v_keys_573_, lean_object* v_vals_574_, lean_object* v_i_575_, lean_object* v_k_576_){
_start:
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_array_get_size(v_keys_573_);
v___x_578_ = lean_nat_dec_lt(v_i_575_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; 
lean_dec(v_k_576_);
lean_dec(v_i_575_);
lean_dec_ref(v_inst_572_);
v___x_579_ = lean_box(0);
return v___x_579_;
}
else
{
lean_object* v_k_x27_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_k_x27_580_ = lean_array_fget_borrowed(v_keys_573_, v_i_575_);
lean_inc_ref(v_inst_572_);
lean_inc(v_k_x27_580_);
lean_inc(v_k_576_);
v___x_581_ = lean_apply_2(v_inst_572_, v_k_576_, v_k_x27_580_);
v___x_582_ = lean_unbox(v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_add(v_i_575_, v___x_583_);
lean_dec(v_i_575_);
v_i_575_ = v___x_584_;
goto _start;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_k_576_);
lean_dec_ref(v_inst_572_);
v___x_586_ = lean_array_fget_borrowed(v_vals_574_, v_i_575_);
lean_dec(v_i_575_);
lean_inc(v___x_586_);
v___x_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___redArg___boxed(lean_object* v_inst_588_, lean_object* v_keys_589_, lean_object* v_vals_590_, lean_object* v_i_591_, lean_object* v_k_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_588_, v_keys_589_, v_vals_590_, v_i_591_, v_k_592_);
lean_dec_ref(v_vals_590_);
lean_dec_ref(v_keys_589_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux(lean_object* v_00_u03b1_594_, lean_object* v_00_u03b2_595_, lean_object* v_inst_596_, lean_object* v_keys_597_, lean_object* v_vals_598_, lean_object* v_heq_599_, lean_object* v_i_600_, lean_object* v_k_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_596_, v_keys_597_, v_vals_598_, v_i_600_, v_k_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___boxed(lean_object* v_00_u03b1_603_, lean_object* v_00_u03b2_604_, lean_object* v_inst_605_, lean_object* v_keys_606_, lean_object* v_vals_607_, lean_object* v_heq_608_, lean_object* v_i_609_, lean_object* v_k_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_PersistentHashMap_findAtAux(v_00_u03b1_603_, v_00_u03b2_604_, v_inst_605_, v_keys_606_, v_vals_607_, v_heq_608_, v_i_609_, v_k_610_);
lean_dec_ref(v_vals_607_);
lean_dec_ref(v_keys_606_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg(lean_object* v_inst_612_, lean_object* v_x_613_, size_t v_x_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
lean_object* v_es_616_; lean_object* v___x_617_; size_t v___x_618_; size_t v___x_619_; lean_object* v_j_620_; lean_object* v___x_621_; 
v_es_616_ = lean_ctor_get(v_x_613_, 0);
lean_inc_ref(v_es_616_);
lean_dec_ref_known(v_x_613_, 1);
v___x_617_ = lean_box(2);
v___x_618_ = ((size_t)31ULL);
v___x_619_ = lean_usize_land(v_x_614_, v___x_618_);
v_j_620_ = lean_usize_to_nat(v___x_619_);
v___x_621_ = lean_array_get(v___x_617_, v_es_616_, v_j_620_);
lean_dec(v_j_620_);
lean_dec_ref(v_es_616_);
switch(lean_obj_tag(v___x_621_))
{
case 0:
{
lean_object* v_key_622_; lean_object* v_val_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_key_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_key_622_);
v_val_623_ = lean_ctor_get(v___x_621_, 1);
lean_inc(v_val_623_);
lean_dec_ref_known(v___x_621_, 2);
v___x_624_ = lean_apply_2(v_inst_612_, v_x_615_, v_key_622_);
v___x_625_ = lean_unbox(v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; 
lean_dec(v_val_623_);
v___x_626_ = lean_box(0);
return v___x_626_;
}
else
{
lean_object* v___x_627_; 
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v_val_623_);
return v___x_627_;
}
}
case 1:
{
lean_object* v_node_628_; size_t v___x_629_; size_t v___x_630_; 
v_node_628_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_node_628_);
lean_dec_ref_known(v___x_621_, 1);
v___x_629_ = ((size_t)5ULL);
v___x_630_ = lean_usize_shift_right(v_x_614_, v___x_629_);
v_x_613_ = v_node_628_;
v_x_614_ = v___x_630_;
goto _start;
}
default: 
{
lean_object* v___x_632_; 
lean_dec(v_x_615_);
lean_dec_ref(v_inst_612_);
v___x_632_ = lean_box(0);
return v___x_632_;
}
}
}
else
{
lean_object* v_ks_633_; lean_object* v_vs_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_ks_633_ = lean_ctor_get(v_x_613_, 0);
lean_inc_ref(v_ks_633_);
v_vs_634_ = lean_ctor_get(v_x_613_, 1);
lean_inc_ref(v_vs_634_);
lean_dec_ref_known(v_x_613_, 2);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = l_Lean_PersistentHashMap_findAtAux___redArg(v_inst_612_, v_ks_633_, v_vs_634_, v___x_635_, v_x_615_);
lean_dec_ref(v_vs_634_);
lean_dec_ref(v_ks_633_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___redArg___boxed(lean_object* v_inst_637_, lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
size_t v_x_118__boxed_641_; lean_object* v_res_642_; 
v_x_118__boxed_641_ = lean_unbox_usize(v_x_639_);
lean_dec(v_x_639_);
v_res_642_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_637_, v_x_638_, v_x_118__boxed_641_, v_x_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux(lean_object* v_00_u03b1_643_, lean_object* v_00_u03b2_644_, lean_object* v_inst_645_, lean_object* v_x_646_, size_t v_x_647_, lean_object* v_x_648_){
_start:
{
lean_object* v___x_649_; 
lean_inc_ref(v_x_646_);
v___x_649_ = l_Lean_PersistentHashMap_findAux___redArg(v_inst_645_, v_x_646_, v_x_647_, v_x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___boxed(lean_object* v_00_u03b1_650_, lean_object* v_00_u03b2_651_, lean_object* v_inst_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
size_t v_x_170__boxed_656_; lean_object* v_res_657_; 
v_x_170__boxed_656_ = lean_unbox_usize(v_x_654_);
lean_dec(v_x_654_);
v_res_657_ = l_Lean_PersistentHashMap_findAux(v_00_u03b1_650_, v_00_u03b2_651_, v_inst_652_, v_x_653_, v_x_170__boxed_656_, v_x_655_);
lean_dec_ref(v_x_653_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
lean_object* v___x_662_; uint64_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
lean_inc(v_x_661_);
v___x_662_ = lean_apply_1(v_x_659_, v_x_661_);
v___x_663_ = lean_unbox_uint64(v___x_662_);
lean_dec_ref(v___x_662_);
v___x_664_ = lean_uint64_to_usize(v___x_663_);
lean_inc_ref(v_x_660_);
v___x_665_ = l_Lean_PersistentHashMap_findAux___redArg(v_x_658_, v_x_660_, v___x_664_, v_x_661_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___redArg___boxed(lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_666_, v_x_667_, v_x_668_, v_x_669_);
lean_dec_ref(v_x_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f(lean_object* v_00_u03b1_671_, lean_object* v_00_u03b2_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_, lean_object* v_x_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_673_, v_x_674_, v_x_675_, v_x_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___boxed(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_PersistentHashMap_find_x3f(v_00_u03b1_678_, v_00_u03b2_679_, v_x_680_, v_x_681_, v_x_682_, v_x_683_);
lean_dec_ref(v_x_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_m_687_, lean_object* v_i_688_, lean_object* v_x_689_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_685_, v_x_686_, v_m_687_, v_i_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed(lean_object* v_x_691_, lean_object* v_x_692_, lean_object* v_m_693_, lean_object* v_i_694_, lean_object* v_x_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0(v_x_691_, v_x_692_, v_m_693_, v_i_694_, v_x_695_);
lean_dec_ref(v_m_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg(lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
lean_object* v___f_699_; 
v___f_699_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_699_, 0, v_x_697_);
lean_closure_set(v___f_699_, 1, v_x_698_);
return v___f_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instGetElemOptionTrue(lean_object* v_00_u03b1_700_, lean_object* v_00_u03b2_701_, lean_object* v_x_702_, lean_object* v_x_703_){
_start:
{
lean_object* v___f_704_; 
v___f_704_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instGetElemOptionTrue___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_704_, 0, v_x_702_);
lean_closure_set(v___f_704_, 1, v_x_703_);
return v___f_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg(lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_m_707_, lean_object* v_a_708_, lean_object* v_b_u2080_709_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___redArg___boxed(lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v_m_714_, lean_object* v_a_715_, lean_object* v_b_u2080_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_PersistentHashMap_findD___redArg(v_x_712_, v_x_713_, v_m_714_, v_a_715_, v_b_u2080_716_);
lean_dec(v_b_u2080_716_);
lean_dec_ref(v_m_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD(lean_object* v_00_u03b1_718_, lean_object* v_00_u03b2_719_, lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_m_722_, lean_object* v_a_723_, lean_object* v_b_u2080_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_720_, v_x_721_, v_m_722_, v_a_723_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_inc(v_b_u2080_724_);
return v_b_u2080_724_;
}
else
{
lean_object* v_val_726_; 
v_val_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_val_726_);
lean_dec_ref_known(v___x_725_, 1);
return v_val_726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findD___boxed(lean_object* v_00_u03b1_727_, lean_object* v_00_u03b2_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_m_731_, lean_object* v_a_732_, lean_object* v_b_u2080_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_PersistentHashMap_findD(v_00_u03b1_727_, v_00_u03b2_728_, v_x_729_, v_x_730_, v_m_731_, v_a_732_, v_b_u2080_733_);
lean_dec(v_b_u2080_733_);
lean_dec_ref(v_m_731_);
return v_res_734_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_738_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__2));
v___x_739_ = lean_unsigned_to_nat(14u);
v___x_740_ = lean_unsigned_to_nat(178u);
v___x_741_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__1));
v___x_742_ = ((lean_object*)(l_Lean_PersistentHashMap_find_x21___redArg___closed__0));
v___x_743_ = l_mkPanicMessageWithDecl(v___x_742_, v___x_741_, v___x_740_, v___x_739_, v___x_738_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg(lean_object* v_x_744_, lean_object* v_x_745_, lean_object* v_inst_746_, lean_object* v_m_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_744_, v_x_745_, v_m_747_, v_a_748_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_751_ = l_panic___redArg(v_inst_746_, v___x_750_);
return v___x_751_;
}
else
{
lean_object* v_val_752_; 
v_val_752_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v___x_749_, 1);
return v_val_752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___redArg___boxed(lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_inst_755_, lean_object* v_m_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_PersistentHashMap_find_x21___redArg(v_x_753_, v_x_754_, v_inst_755_, v_m_756_, v_a_757_);
lean_dec_ref(v_m_756_);
lean_dec(v_inst_755_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21(lean_object* v_00_u03b1_759_, lean_object* v_00_u03b2_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_inst_763_, lean_object* v_m_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_PersistentHashMap_find_x3f___redArg(v_x_761_, v_x_762_, v_m_764_, v_a_765_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = lean_obj_once(&l_Lean_PersistentHashMap_find_x21___redArg___closed__3, &l_Lean_PersistentHashMap_find_x21___redArg___closed__3_once, _init_l_Lean_PersistentHashMap_find_x21___redArg___closed__3);
v___x_768_ = l_panic___redArg(v_inst_763_, v___x_767_);
return v___x_768_;
}
else
{
lean_object* v_val_769_; 
v_val_769_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v___x_766_, 1);
return v_val_769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x21___boxed(lean_object* v_00_u03b1_770_, lean_object* v_00_u03b2_771_, lean_object* v_x_772_, lean_object* v_x_773_, lean_object* v_inst_774_, lean_object* v_m_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_PersistentHashMap_find_x21(v_00_u03b1_770_, v_00_u03b2_771_, v_x_772_, v_x_773_, v_inst_774_, v_m_775_, v_a_776_);
lean_dec_ref(v_m_775_);
lean_dec(v_inst_774_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg(lean_object* v_inst_778_, lean_object* v_keys_779_, lean_object* v_vals_780_, lean_object* v_i_781_, lean_object* v_k_782_){
_start:
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = lean_array_get_size(v_keys_779_);
v___x_784_ = lean_nat_dec_lt(v_i_781_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v_k_782_);
lean_dec(v_i_781_);
lean_dec_ref(v_inst_778_);
v___x_785_ = lean_box(0);
return v___x_785_;
}
else
{
lean_object* v_k_x27_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_k_x27_786_ = lean_array_fget_borrowed(v_keys_779_, v_i_781_);
lean_inc_ref(v_inst_778_);
lean_inc(v_k_x27_786_);
lean_inc(v_k_782_);
v___x_787_ = lean_apply_2(v_inst_778_, v_k_782_, v_k_x27_786_);
v___x_788_ = lean_unbox(v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_i_781_, v___x_789_);
lean_dec(v_i_781_);
v_i_781_ = v___x_790_;
goto _start;
}
else
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_dec(v_k_782_);
lean_dec_ref(v_inst_778_);
v___x_792_ = lean_array_fget_borrowed(v_vals_780_, v_i_781_);
lean_dec(v_i_781_);
lean_inc(v___x_792_);
lean_inc(v_k_x27_786_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v_k_x27_786_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___redArg___boxed(lean_object* v_inst_795_, lean_object* v_keys_796_, lean_object* v_vals_797_, lean_object* v_i_798_, lean_object* v_k_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_795_, v_keys_796_, v_vals_797_, v_i_798_, v_k_799_);
lean_dec_ref(v_vals_797_);
lean_dec_ref(v_keys_796_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_inst_803_, lean_object* v_keys_804_, lean_object* v_vals_805_, lean_object* v_heq_806_, lean_object* v_i_807_, lean_object* v_k_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_803_, v_keys_804_, v_vals_805_, v_i_807_, v_k_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAtAux___boxed(lean_object* v_00_u03b1_810_, lean_object* v_00_u03b2_811_, lean_object* v_inst_812_, lean_object* v_keys_813_, lean_object* v_vals_814_, lean_object* v_heq_815_, lean_object* v_i_816_, lean_object* v_k_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_PersistentHashMap_findEntryAtAux(v_00_u03b1_810_, v_00_u03b2_811_, v_inst_812_, v_keys_813_, v_vals_814_, v_heq_815_, v_i_816_, v_k_817_);
lean_dec_ref(v_vals_814_);
lean_dec_ref(v_keys_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg(lean_object* v_inst_819_, lean_object* v_x_820_, size_t v_x_821_, lean_object* v_x_822_){
_start:
{
if (lean_obj_tag(v_x_820_) == 0)
{
lean_object* v_es_823_; lean_object* v___x_824_; size_t v___x_825_; size_t v___x_826_; lean_object* v_j_827_; lean_object* v___x_828_; 
v_es_823_ = lean_ctor_get(v_x_820_, 0);
lean_inc_ref(v_es_823_);
lean_dec_ref_known(v_x_820_, 1);
v___x_824_ = lean_box(2);
v___x_825_ = ((size_t)31ULL);
v___x_826_ = lean_usize_land(v_x_821_, v___x_825_);
v_j_827_ = lean_usize_to_nat(v___x_826_);
v___x_828_ = lean_array_get(v___x_824_, v_es_823_, v_j_827_);
lean_dec(v_j_827_);
lean_dec_ref(v_es_823_);
switch(lean_obj_tag(v___x_828_))
{
case 0:
{
lean_object* v_key_829_; lean_object* v_val_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_key_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc_n(v_key_829_, 2);
v_val_830_ = lean_ctor_get(v___x_828_, 1);
lean_inc(v_val_830_);
lean_dec_ref_known(v___x_828_, 2);
v___x_831_ = lean_apply_2(v_inst_819_, v_x_822_, v_key_829_);
v___x_832_ = lean_unbox(v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
lean_dec(v_val_830_);
lean_dec(v_key_829_);
v___x_833_ = lean_box(0);
return v___x_833_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v_key_829_);
lean_ctor_set(v___x_834_, 1, v_val_830_);
v___x_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
return v___x_835_;
}
}
case 1:
{
lean_object* v_node_836_; size_t v___x_837_; size_t v___x_838_; 
v_node_836_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_node_836_);
lean_dec_ref_known(v___x_828_, 1);
v___x_837_ = ((size_t)5ULL);
v___x_838_ = lean_usize_shift_right(v_x_821_, v___x_837_);
v_x_820_ = v_node_836_;
v_x_821_ = v___x_838_;
goto _start;
}
default: 
{
lean_object* v___x_840_; 
lean_dec(v_x_822_);
lean_dec_ref(v_inst_819_);
v___x_840_ = lean_box(0);
return v___x_840_;
}
}
}
else
{
lean_object* v_ks_841_; lean_object* v_vs_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_ks_841_ = lean_ctor_get(v_x_820_, 0);
lean_inc_ref(v_ks_841_);
v_vs_842_ = lean_ctor_get(v_x_820_, 1);
lean_inc_ref(v_vs_842_);
lean_dec_ref_known(v_x_820_, 2);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = l_Lean_PersistentHashMap_findEntryAtAux___redArg(v_inst_819_, v_ks_841_, v_vs_842_, v___x_843_, v_x_822_);
lean_dec_ref(v_vs_842_);
lean_dec_ref(v_ks_841_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___redArg___boxed(lean_object* v_inst_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
size_t v_x_121__boxed_849_; lean_object* v_res_850_; 
v_x_121__boxed_849_ = lean_unbox_usize(v_x_847_);
lean_dec(v_x_847_);
v_res_850_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_845_, v_x_846_, v_x_121__boxed_849_, v_x_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux(lean_object* v_00_u03b1_851_, lean_object* v_00_u03b2_852_, lean_object* v_inst_853_, lean_object* v_x_854_, size_t v_x_855_, lean_object* v_x_856_){
_start:
{
lean_object* v___x_857_; 
lean_inc_ref(v_x_854_);
v___x_857_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_inst_853_, v_x_854_, v_x_855_, v_x_856_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntryAux___boxed(lean_object* v_00_u03b1_858_, lean_object* v_00_u03b2_859_, lean_object* v_inst_860_, lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
size_t v_x_175__boxed_864_; lean_object* v_res_865_; 
v_x_175__boxed_864_ = lean_unbox_usize(v_x_862_);
lean_dec(v_x_862_);
v_res_865_ = l_Lean_PersistentHashMap_findEntryAux(v_00_u03b1_858_, v_00_u03b2_859_, v_inst_860_, v_x_861_, v_x_175__boxed_864_, v_x_863_);
lean_dec_ref(v_x_861_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v___x_870_; uint64_t v___x_871_; size_t v___x_872_; lean_object* v___x_873_; 
lean_inc(v_x_869_);
v___x_870_ = lean_apply_1(v_x_867_, v_x_869_);
v___x_871_ = lean_unbox_uint64(v___x_870_);
lean_dec_ref(v___x_870_);
v___x_872_ = lean_uint64_to_usize(v___x_871_);
lean_inc_ref(v_x_868_);
v___x_873_ = l_Lean_PersistentHashMap_findEntryAux___redArg(v_x_866_, v_x_868_, v___x_872_, v_x_869_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg___boxed(lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_874_, v_x_875_, v_x_876_, v_x_877_);
lean_dec_ref(v_x_876_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f(lean_object* v_00_u03b1_879_, lean_object* v_00_u03b2_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_881_, v_x_882_, v_x_883_, v_x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findEntry_x3f___boxed(lean_object* v_00_u03b1_886_, lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_PersistentHashMap_findEntry_x3f(v_00_u03b1_886_, v_00_u03b2_887_, v_x_888_, v_x_889_, v_x_890_, v_x_891_);
lean_dec_ref(v_x_890_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg(lean_object* v_inst_893_, lean_object* v_keys_894_, lean_object* v_i_895_, lean_object* v_k_896_, lean_object* v_k_u2080_897_){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_array_get_size(v_keys_894_);
v___x_899_ = lean_nat_dec_lt(v_i_895_, v___x_898_);
if (v___x_899_ == 0)
{
lean_dec(v_k_896_);
lean_dec(v_i_895_);
lean_dec_ref(v_inst_893_);
lean_inc(v_k_u2080_897_);
return v_k_u2080_897_;
}
else
{
lean_object* v_k_x27_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v_k_x27_900_ = lean_array_fget_borrowed(v_keys_894_, v_i_895_);
lean_inc_ref(v_inst_893_);
lean_inc(v_k_x27_900_);
lean_inc(v_k_896_);
v___x_901_ = lean_apply_2(v_inst_893_, v_k_896_, v_k_x27_900_);
v___x_902_ = lean_unbox(v___x_901_);
if (v___x_902_ == 0)
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_add(v_i_895_, v___x_903_);
lean_dec(v_i_895_);
v_i_895_ = v___x_904_;
goto _start;
}
else
{
lean_dec(v_k_896_);
lean_dec(v_i_895_);
lean_dec_ref(v_inst_893_);
lean_inc(v_k_x27_900_);
return v_k_x27_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___redArg___boxed(lean_object* v_inst_906_, lean_object* v_keys_907_, lean_object* v_i_908_, lean_object* v_k_909_, lean_object* v_k_u2080_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_906_, v_keys_907_, v_i_908_, v_k_909_, v_k_u2080_910_);
lean_dec(v_k_u2080_910_);
lean_dec_ref(v_keys_907_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux(lean_object* v_00_u03b1_912_, lean_object* v_00_u03b2_913_, lean_object* v_inst_914_, lean_object* v_keys_915_, lean_object* v_vals_916_, lean_object* v_heq_917_, lean_object* v_i_918_, lean_object* v_k_919_, lean_object* v_k_u2080_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_914_, v_keys_915_, v_i_918_, v_k_919_, v_k_u2080_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAtAux___boxed(lean_object* v_00_u03b1_922_, lean_object* v_00_u03b2_923_, lean_object* v_inst_924_, lean_object* v_keys_925_, lean_object* v_vals_926_, lean_object* v_heq_927_, lean_object* v_i_928_, lean_object* v_k_929_, lean_object* v_k_u2080_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_PersistentHashMap_findKeyDAtAux(v_00_u03b1_922_, v_00_u03b2_923_, v_inst_924_, v_keys_925_, v_vals_926_, v_heq_927_, v_i_928_, v_k_929_, v_k_u2080_930_);
lean_dec(v_k_u2080_930_);
lean_dec_ref(v_vals_926_);
lean_dec_ref(v_keys_925_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object* v_inst_932_, lean_object* v_x_933_, size_t v_x_934_, lean_object* v_x_935_, lean_object* v_x_936_){
_start:
{
if (lean_obj_tag(v_x_933_) == 0)
{
lean_object* v_es_937_; lean_object* v___x_938_; size_t v___x_939_; size_t v___x_940_; lean_object* v_j_941_; lean_object* v___x_942_; 
v_es_937_ = lean_ctor_get(v_x_933_, 0);
lean_inc_ref(v_es_937_);
lean_dec_ref_known(v_x_933_, 1);
v___x_938_ = lean_box(2);
v___x_939_ = ((size_t)31ULL);
v___x_940_ = lean_usize_land(v_x_934_, v___x_939_);
v_j_941_ = lean_usize_to_nat(v___x_940_);
v___x_942_ = lean_array_get(v___x_938_, v_es_937_, v_j_941_);
lean_dec(v_j_941_);
lean_dec_ref(v_es_937_);
switch(lean_obj_tag(v___x_942_))
{
case 0:
{
lean_object* v_key_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
v_key_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc_n(v_key_943_, 2);
lean_dec_ref_known(v___x_942_, 2);
v___x_944_ = lean_apply_2(v_inst_932_, v_x_935_, v_key_943_);
v___x_945_ = lean_unbox(v___x_944_);
if (v___x_945_ == 0)
{
lean_dec(v_key_943_);
lean_inc(v_x_936_);
return v_x_936_;
}
else
{
return v_key_943_;
}
}
case 1:
{
lean_object* v_node_946_; size_t v___x_947_; size_t v___x_948_; 
v_node_946_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_node_946_);
lean_dec_ref_known(v___x_942_, 1);
v___x_947_ = ((size_t)5ULL);
v___x_948_ = lean_usize_shift_right(v_x_934_, v___x_947_);
v_x_933_ = v_node_946_;
v_x_934_ = v___x_948_;
goto _start;
}
default: 
{
lean_dec(v_x_935_);
lean_dec_ref(v_inst_932_);
lean_inc(v_x_936_);
return v_x_936_;
}
}
}
else
{
lean_object* v_ks_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_ks_950_ = lean_ctor_get(v_x_933_, 0);
lean_inc_ref(v_ks_950_);
lean_dec_ref_known(v_x_933_, 2);
v___x_951_ = lean_unsigned_to_nat(0u);
v___x_952_ = l_Lean_PersistentHashMap_findKeyDAtAux___redArg(v_inst_932_, v_ks_950_, v___x_951_, v_x_935_, v_x_936_);
lean_dec_ref(v_ks_950_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg___boxed(lean_object* v_inst_953_, lean_object* v_x_954_, lean_object* v_x_955_, lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
size_t v_x_113__boxed_958_; lean_object* v_res_959_; 
v_x_113__boxed_958_ = lean_unbox_usize(v_x_955_);
lean_dec(v_x_955_);
v_res_959_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_953_, v_x_954_, v_x_113__boxed_958_, v_x_956_, v_x_957_);
lean_dec(v_x_957_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux(lean_object* v_00_u03b1_960_, lean_object* v_00_u03b2_961_, lean_object* v_inst_962_, lean_object* v_x_963_, size_t v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_inst_962_, v_x_963_, v_x_964_, v_x_965_, v_x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyDAux___boxed(lean_object* v_00_u03b1_968_, lean_object* v_00_u03b2_969_, lean_object* v_inst_970_, lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_x_973_, lean_object* v_x_974_){
_start:
{
size_t v_x_160__boxed_975_; lean_object* v_res_976_; 
v_x_160__boxed_975_ = lean_unbox_usize(v_x_972_);
lean_dec(v_x_972_);
v_res_976_ = l_Lean_PersistentHashMap_findKeyDAux(v_00_u03b1_968_, v_00_u03b2_969_, v_inst_970_, v_x_971_, v_x_160__boxed_975_, v_x_973_, v_x_974_);
lean_dec(v_x_974_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg(lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v_m_979_, lean_object* v_a_980_, lean_object* v_a_u2080_981_){
_start:
{
lean_object* v___x_982_; uint64_t v___x_983_; size_t v___x_984_; lean_object* v___x_985_; 
lean_inc(v_a_980_);
v___x_982_ = lean_apply_1(v_x_978_, v_a_980_);
v___x_983_ = lean_unbox_uint64(v___x_982_);
lean_dec_ref(v___x_982_);
v___x_984_ = lean_uint64_to_usize(v___x_983_);
v___x_985_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_977_, v_m_979_, v___x_984_, v_a_980_, v_a_u2080_981_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___redArg___boxed(lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v_m_988_, lean_object* v_a_989_, lean_object* v_a_u2080_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_PersistentHashMap_findKeyD___redArg(v_x_986_, v_x_987_, v_m_988_, v_a_989_, v_a_u2080_990_);
lean_dec(v_a_u2080_990_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD(lean_object* v_00_u03b1_992_, lean_object* v_00_u03b2_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_m_996_, lean_object* v_a_997_, lean_object* v_a_u2080_998_){
_start:
{
lean_object* v___x_999_; uint64_t v___x_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
lean_inc(v_a_997_);
v___x_999_ = lean_apply_1(v_x_995_, v_a_997_);
v___x_1000_ = lean_unbox_uint64(v___x_999_);
lean_dec_ref(v___x_999_);
v___x_1001_ = lean_uint64_to_usize(v___x_1000_);
v___x_1002_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_994_, v_m_996_, v___x_1001_, v_a_997_, v_a_u2080_998_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findKeyD___boxed(lean_object* v_00_u03b1_1003_, lean_object* v_00_u03b2_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_m_1007_, lean_object* v_a_1008_, lean_object* v_a_u2080_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_PersistentHashMap_findKeyD(v_00_u03b1_1003_, v_00_u03b2_1004_, v_x_1005_, v_x_1006_, v_m_1007_, v_a_1008_, v_a_u2080_1009_);
lean_dec(v_a_u2080_1009_);
return v_res_1010_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___redArg(lean_object* v_inst_1011_, lean_object* v_keys_1012_, lean_object* v_i_1013_, lean_object* v_k_1014_){
_start:
{
lean_object* v___x_1015_; uint8_t v___x_1016_; 
v___x_1015_ = lean_array_get_size(v_keys_1012_);
v___x_1016_ = lean_nat_dec_lt(v_i_1013_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_dec(v_k_1014_);
lean_dec(v_i_1013_);
lean_dec_ref(v_inst_1011_);
return v___x_1016_;
}
else
{
lean_object* v_k_x27_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v_k_x27_1017_ = lean_array_fget_borrowed(v_keys_1012_, v_i_1013_);
lean_inc_ref(v_inst_1011_);
lean_inc(v_k_x27_1017_);
lean_inc(v_k_1014_);
v___x_1018_ = lean_apply_2(v_inst_1011_, v_k_1014_, v_k_x27_1017_);
v___x_1019_ = lean_unbox(v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_add(v_i_1013_, v___x_1020_);
lean_dec(v_i_1013_);
v_i_1013_ = v___x_1021_;
goto _start;
}
else
{
lean_dec(v_k_1014_);
lean_dec(v_i_1013_);
lean_dec_ref(v_inst_1011_);
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___redArg___boxed(lean_object* v_inst_1023_, lean_object* v_keys_1024_, lean_object* v_i_1025_, lean_object* v_k_1026_){
_start:
{
uint8_t v_res_1027_; lean_object* v_r_1028_; 
v_res_1027_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1023_, v_keys_1024_, v_i_1025_, v_k_1026_);
lean_dec_ref(v_keys_1024_);
v_r_1028_ = lean_box(v_res_1027_);
return v_r_1028_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux(lean_object* v_00_u03b1_1029_, lean_object* v_00_u03b2_1030_, lean_object* v_inst_1031_, lean_object* v_keys_1032_, lean_object* v_vals_1033_, lean_object* v_heq_1034_, lean_object* v_i_1035_, lean_object* v_k_1036_){
_start:
{
uint8_t v___x_1037_; 
v___x_1037_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1031_, v_keys_1032_, v_i_1035_, v_k_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___boxed(lean_object* v_00_u03b1_1038_, lean_object* v_00_u03b2_1039_, lean_object* v_inst_1040_, lean_object* v_keys_1041_, lean_object* v_vals_1042_, lean_object* v_heq_1043_, lean_object* v_i_1044_, lean_object* v_k_1045_){
_start:
{
uint8_t v_res_1046_; lean_object* v_r_1047_; 
v_res_1046_ = l_Lean_PersistentHashMap_containsAtAux(v_00_u03b1_1038_, v_00_u03b2_1039_, v_inst_1040_, v_keys_1041_, v_vals_1042_, v_heq_1043_, v_i_1044_, v_k_1045_);
lean_dec_ref(v_vals_1042_);
lean_dec_ref(v_keys_1041_);
v_r_1047_ = lean_box(v_res_1046_);
return v_r_1047_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___redArg(lean_object* v_inst_1048_, lean_object* v_x_1049_, size_t v_x_1050_, lean_object* v_x_1051_){
_start:
{
if (lean_obj_tag(v_x_1049_) == 0)
{
lean_object* v_es_1052_; lean_object* v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; lean_object* v_j_1056_; lean_object* v___x_1057_; 
v_es_1052_ = lean_ctor_get(v_x_1049_, 0);
lean_inc_ref(v_es_1052_);
lean_dec_ref_known(v_x_1049_, 1);
v___x_1053_ = lean_box(2);
v___x_1054_ = ((size_t)31ULL);
v___x_1055_ = lean_usize_land(v_x_1050_, v___x_1054_);
v_j_1056_ = lean_usize_to_nat(v___x_1055_);
v___x_1057_ = lean_array_get(v___x_1053_, v_es_1052_, v_j_1056_);
lean_dec(v_j_1056_);
lean_dec_ref(v_es_1052_);
switch(lean_obj_tag(v___x_1057_))
{
case 0:
{
lean_object* v_key_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v_key_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_key_1058_);
lean_dec_ref_known(v___x_1057_, 2);
v___x_1059_ = lean_apply_2(v_inst_1048_, v_x_1051_, v_key_1058_);
v___x_1060_ = lean_unbox(v___x_1059_);
return v___x_1060_;
}
case 1:
{
lean_object* v_node_1061_; size_t v___x_1062_; size_t v___x_1063_; 
v_node_1061_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_node_1061_);
lean_dec_ref_known(v___x_1057_, 1);
v___x_1062_ = ((size_t)5ULL);
v___x_1063_ = lean_usize_shift_right(v_x_1050_, v___x_1062_);
v_x_1049_ = v_node_1061_;
v_x_1050_ = v___x_1063_;
goto _start;
}
default: 
{
uint8_t v___x_1065_; 
lean_dec(v_x_1051_);
lean_dec_ref(v_inst_1048_);
v___x_1065_ = 0;
return v___x_1065_;
}
}
}
else
{
lean_object* v_ks_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_ks_1066_ = lean_ctor_get(v_x_1049_, 0);
lean_inc_ref(v_ks_1066_);
lean_dec_ref_known(v_x_1049_, 2);
v___x_1067_ = lean_unsigned_to_nat(0u);
v___x_1068_ = l_Lean_PersistentHashMap_containsAtAux___redArg(v_inst_1048_, v_ks_1066_, v___x_1067_, v_x_1051_);
lean_dec_ref(v_ks_1066_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___redArg___boxed(lean_object* v_inst_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
size_t v_x_104__boxed_1073_; uint8_t v_res_1074_; lean_object* v_r_1075_; 
v_x_104__boxed_1073_ = lean_unbox_usize(v_x_1071_);
lean_dec(v_x_1071_);
v_res_1074_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1069_, v_x_1070_, v_x_104__boxed_1073_, v_x_1072_);
v_r_1075_ = lean_box(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux(lean_object* v_00_u03b1_1076_, lean_object* v_00_u03b2_1077_, lean_object* v_inst_1078_, lean_object* v_x_1079_, size_t v_x_1080_, lean_object* v_x_1081_){
_start:
{
uint8_t v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1078_, v_x_1079_, v_x_1080_, v_x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___boxed(lean_object* v_00_u03b1_1083_, lean_object* v_00_u03b2_1084_, lean_object* v_inst_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
size_t v_x_150__boxed_1089_; uint8_t v_res_1090_; lean_object* v_r_1091_; 
v_x_150__boxed_1089_ = lean_unbox_usize(v_x_1087_);
lean_dec(v_x_1087_);
v_res_1090_ = l_Lean_PersistentHashMap_containsAux(v_00_u03b1_1083_, v_00_u03b2_1084_, v_inst_1085_, v_x_1086_, v_x_150__boxed_1089_, v_x_1088_);
v_r_1091_ = lean_box(v_res_1090_);
return v_r_1091_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_x_1094_, lean_object* v_x_1095_){
_start:
{
lean_object* v___x_1096_; uint64_t v___x_1097_; size_t v___x_1098_; uint8_t v___x_1099_; 
lean_inc(v_x_1095_);
v___x_1096_ = lean_apply_1(v_inst_1093_, v_x_1095_);
v___x_1097_ = lean_unbox_uint64(v___x_1096_);
lean_dec_ref(v___x_1096_);
v___x_1098_ = lean_uint64_to_usize(v___x_1097_);
v___x_1099_ = l_Lean_PersistentHashMap_containsAux___redArg(v_inst_1092_, v_x_1094_, v___x_1098_, v_x_1095_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___redArg___boxed(lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_){
_start:
{
uint8_t v_res_1104_; lean_object* v_r_1105_; 
v_res_1104_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1100_, v_inst_1101_, v_x_1102_, v_x_1103_);
v_r_1105_ = lean_box(v_res_1104_);
return v_r_1105_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains(lean_object* v_00_u03b1_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = l_Lean_PersistentHashMap_contains___redArg(v_inst_1108_, v_inst_1109_, v_x_1110_, v_x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___boxed(lean_object* v_00_u03b1_1113_, lean_object* v_00_u03b2_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
uint8_t v_res_1119_; lean_object* v_r_1120_; 
v_res_1119_ = l_Lean_PersistentHashMap_contains(v_00_u03b1_1113_, v_00_u03b2_1114_, v_inst_1115_, v_inst_1116_, v_x_1117_, v_x_1118_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg(lean_object* v_a_1121_, lean_object* v_i_1122_, lean_object* v_acc_1123_){
_start:
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = lean_array_get_size(v_a_1121_);
v___x_1125_ = lean_nat_dec_lt(v_i_1122_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_dec(v_i_1122_);
return v_acc_1123_;
}
else
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_array_fget(v_a_1121_, v_i_1122_);
switch(lean_obj_tag(v___x_1126_))
{
case 0:
{
if (lean_obj_tag(v_acc_1123_) == 0)
{
lean_object* v_key_1127_; lean_object* v_val_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1139_; 
v_key_1127_ = lean_ctor_get(v___x_1126_, 0);
v_val_1128_ = lean_ctor_get(v___x_1126_, 1);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1130_ = v___x_1126_;
v_isShared_1131_ = v_isSharedCheck_1139_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_val_1128_);
lean_inc(v_key_1127_);
lean_dec(v___x_1126_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1139_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = lean_nat_add(v_i_1122_, v___x_1132_);
lean_dec(v_i_1122_);
if (v_isShared_1131_ == 0)
{
v___x_1135_ = v___x_1130_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_key_1127_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_val_1128_);
v___x_1135_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
v_i_1122_ = v___x_1133_;
v_acc_1123_ = v___x_1136_;
goto _start;
}
}
}
else
{
lean_object* v___x_1140_; 
lean_dec_ref_known(v_acc_1123_, 1);
lean_dec_ref_known(v___x_1126_, 2);
lean_dec(v_i_1122_);
v___x_1140_ = lean_box(0);
return v___x_1140_;
}
}
case 1:
{
lean_object* v___x_1141_; 
lean_dec_ref_known(v___x_1126_, 1);
lean_dec(v_acc_1123_);
lean_dec(v_i_1122_);
v___x_1141_ = lean_box(0);
return v___x_1141_;
}
default: 
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = lean_nat_add(v_i_1122_, v___x_1142_);
lean_dec(v_i_1122_);
v_i_1122_ = v___x_1143_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___redArg___boxed(lean_object* v_a_1145_, lean_object* v_i_1146_, lean_object* v_acc_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1145_, v_i_1146_, v_acc_1147_);
lean_dec_ref(v_a_1145_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries(lean_object* v_00_u03b1_1149_, lean_object* v_00_u03b2_1150_, lean_object* v_a_1151_, lean_object* v_i_1152_, lean_object* v_acc_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_a_1151_, v_i_1152_, v_acc_1153_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryEntries___boxed(lean_object* v_00_u03b1_1155_, lean_object* v_00_u03b2_1156_, lean_object* v_a_1157_, lean_object* v_i_1158_, lean_object* v_acc_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_PersistentHashMap_isUnaryEntries(v_00_u03b1_1155_, v_00_u03b2_1156_, v_a_1157_, v_i_1158_, v_acc_1159_);
lean_dec_ref(v_a_1157_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object* v_x_1161_){
_start:
{
if (lean_obj_tag(v_x_1161_) == 0)
{
lean_object* v_es_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_es_1162_ = lean_ctor_get(v_x_1161_, 0);
lean_inc_ref(v_es_1162_);
lean_dec_ref_known(v_x_1161_, 1);
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_box(0);
v___x_1165_ = l_Lean_PersistentHashMap_isUnaryEntries___redArg(v_es_1162_, v___x_1163_, v___x_1164_);
lean_dec_ref(v_es_1162_);
return v___x_1165_;
}
else
{
lean_object* v_ks_1166_; lean_object* v_vs_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1182_; 
v_ks_1166_ = lean_ctor_get(v_x_1161_, 0);
v_vs_1167_ = lean_ctor_get(v_x_1161_, 1);
v_isSharedCheck_1182_ = !lean_is_exclusive(v_x_1161_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1169_ = v_x_1161_;
v_isShared_1170_ = v_isSharedCheck_1182_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_vs_1167_);
lean_inc(v_ks_1166_);
lean_dec(v_x_1161_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1182_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1171_ = lean_unsigned_to_nat(1u);
v___x_1172_ = lean_array_get_size(v_ks_1166_);
v___x_1173_ = lean_nat_dec_eq(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
lean_del_object(v___x_1169_);
lean_dec_ref(v_vs_1167_);
lean_dec_ref(v_ks_1166_);
v___x_1174_ = lean_box(0);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1179_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = lean_array_fget(v_ks_1166_, v___x_1175_);
lean_dec_ref(v_ks_1166_);
v___x_1177_ = lean_array_fget(v_vs_1167_, v___x_1175_);
lean_dec_ref(v_vs_1167_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set_tag(v___x_1169_, 0);
lean_ctor_set(v___x_1169_, 1, v___x_1177_);
lean_ctor_set(v___x_1169_, 0, v___x_1176_);
v___x_1179_ = v___x_1169_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v___x_1177_);
v___x_1179_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_isUnaryNode(lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg(lean_object* v_inst_1187_, lean_object* v_x_1188_, size_t v_x_1189_, lean_object* v_x_1190_){
_start:
{
if (lean_obj_tag(v_x_1188_) == 0)
{
lean_object* v_es_1191_; lean_object* v___x_1192_; size_t v___x_1193_; size_t v___x_1194_; lean_object* v_j_1195_; lean_object* v_entry_1196_; 
v_es_1191_ = lean_ctor_get(v_x_1188_, 0);
v___x_1192_ = lean_box(2);
v___x_1193_ = ((size_t)31ULL);
v___x_1194_ = lean_usize_land(v_x_1189_, v___x_1193_);
v_j_1195_ = lean_usize_to_nat(v___x_1194_);
v_entry_1196_ = lean_array_get(v___x_1192_, v_es_1191_, v_j_1195_);
switch(lean_obj_tag(v_entry_1196_))
{
case 0:
{
lean_object* v_key_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v_key_1197_ = lean_ctor_get(v_entry_1196_, 0);
lean_inc(v_key_1197_);
lean_dec_ref_known(v_entry_1196_, 2);
v___x_1198_ = lean_apply_2(v_inst_1187_, v_x_1190_, v_key_1197_);
v___x_1199_ = lean_unbox(v___x_1198_);
if (v___x_1199_ == 0)
{
lean_dec(v_j_1195_);
return v_x_1188_;
}
else
{
lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1207_; 
lean_inc_ref(v_es_1191_);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_x_1188_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v_x_1188_, 0);
lean_dec(v_unused_1208_);
v___x_1201_ = v_x_1188_;
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
else
{
lean_dec(v_x_1188_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_array_set(v_es_1191_, v_j_1195_, v___x_1192_);
lean_dec(v_j_1195_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1203_);
v___x_1205_ = v___x_1201_;
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
}
case 1:
{
lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1243_; 
lean_inc_ref(v_es_1191_);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_x_1188_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v_x_1188_, 0);
lean_dec(v_unused_1244_);
v___x_1210_ = v_x_1188_;
v_isShared_1211_ = v_isSharedCheck_1243_;
goto v_resetjp_1209_;
}
else
{
lean_dec(v_x_1188_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1243_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v_node_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1242_; 
v_node_1212_ = lean_ctor_get(v_entry_1196_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_entry_1196_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1214_ = v_entry_1196_;
v_isShared_1215_ = v_isSharedCheck_1242_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_node_1212_);
lean_dec(v_entry_1196_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1242_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
size_t v___x_1216_; lean_object* v_entries_1217_; size_t v___x_1218_; lean_object* v_newNode_1219_; lean_object* v___x_1220_; 
v___x_1216_ = ((size_t)5ULL);
v_entries_1217_ = lean_array_set(v_es_1191_, v_j_1195_, v___x_1192_);
v___x_1218_ = lean_usize_shift_right(v_x_1189_, v___x_1216_);
v_newNode_1219_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1187_, v_node_1212_, v___x_1218_, v_x_1190_);
lean_inc_ref(v_newNode_1219_);
v___x_1220_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1219_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v___x_1222_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v_newNode_1219_);
v___x_1222_ = v___x_1214_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_newNode_1219_);
v___x_1222_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_array_set(v_entries_1217_, v_j_1195_, v___x_1222_);
lean_dec(v_j_1195_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1223_);
v___x_1225_ = v___x_1210_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_object* v_val_1228_; lean_object* v_fst_1229_; lean_object* v_snd_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref(v_newNode_1219_);
lean_del_object(v___x_1214_);
v_val_1228_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v___x_1220_, 1);
v_fst_1229_ = lean_ctor_get(v_val_1228_, 0);
v_snd_1230_ = lean_ctor_get(v_val_1228_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_val_1228_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1232_ = v_val_1228_;
v_isShared_1233_ = v_isSharedCheck_1241_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_snd_1230_);
lean_inc(v_fst_1229_);
lean_dec(v_val_1228_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1241_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_fst_1229_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_snd_1230_);
v___x_1235_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
v___x_1236_ = lean_array_set(v_entries_1217_, v_j_1195_, v___x_1235_);
lean_dec(v_j_1195_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1236_);
v___x_1238_ = v___x_1210_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
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
}
default: 
{
lean_dec(v_j_1195_);
lean_dec(v_x_1190_);
lean_dec_ref(v_inst_1187_);
return v_x_1188_;
}
}
}
else
{
lean_object* v_ks_1245_; lean_object* v_vs_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1260_; 
v_ks_1245_ = lean_ctor_get(v_x_1188_, 0);
v_vs_1246_ = lean_ctor_get(v_x_1188_, 1);
v_isSharedCheck_1260_ = !lean_is_exclusive(v_x_1188_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1248_ = v_x_1188_;
v_isShared_1249_ = v_isSharedCheck_1260_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_vs_1246_);
lean_inc(v_ks_1245_);
lean_dec(v_x_1188_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1260_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Array_finIdxOf_x3f___redArg(v_inst_1187_, v_ks_1245_, v_x_1190_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v___x_1252_; 
if (v_isShared_1249_ == 0)
{
v___x_1252_ = v___x_1248_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_ks_1245_);
lean_ctor_set(v_reuseFailAlloc_1253_, 1, v_vs_1246_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
else
{
lean_object* v_val_1254_; lean_object* v_keys_x27_1255_; lean_object* v_vals_x27_1256_; lean_object* v___x_1258_; 
v_val_1254_ = lean_ctor_get(v___x_1250_, 0);
lean_inc_n(v_val_1254_, 2);
lean_dec_ref_known(v___x_1250_, 1);
v_keys_x27_1255_ = l_Array_eraseIdx___redArg(v_ks_1245_, v_val_1254_);
v_vals_x27_1256_ = l_Array_eraseIdx___redArg(v_vs_1246_, v_val_1254_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v_vals_x27_1256_);
lean_ctor_set(v___x_1248_, 0, v_keys_x27_1255_);
v___x_1258_ = v___x_1248_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_keys_x27_1255_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_vals_x27_1256_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___redArg___boxed(lean_object* v_inst_1261_, lean_object* v_x_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_){
_start:
{
size_t v_x_202__boxed_1265_; lean_object* v_res_1266_; 
v_x_202__boxed_1265_ = lean_unbox_usize(v_x_1263_);
lean_dec(v_x_1263_);
v_res_1266_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1261_, v_x_1262_, v_x_202__boxed_1265_, v_x_1264_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux(lean_object* v_00_u03b1_1267_, lean_object* v_00_u03b2_1268_, lean_object* v_inst_1269_, lean_object* v_x_1270_, size_t v_x_1271_, lean_object* v_x_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_inst_1269_, v_x_1270_, v_x_1271_, v_x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___boxed(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_inst_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_){
_start:
{
size_t v_x_343__boxed_1280_; lean_object* v_res_1281_; 
v_x_343__boxed_1280_ = lean_unbox_usize(v_x_1278_);
lean_dec(v_x_1278_);
v_res_1281_ = l_Lean_PersistentHashMap_eraseAux(v_00_u03b1_1274_, v_00_u03b2_1275_, v_inst_1276_, v_x_1277_, v_x_343__boxed_1280_, v_x_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object* v_x_1282_, lean_object* v_x_1283_, lean_object* v_x_1284_, lean_object* v_x_1285_){
_start:
{
lean_object* v___x_1286_; uint64_t v___x_1287_; size_t v_h_1288_; lean_object* v___x_1289_; 
lean_inc(v_x_1285_);
v___x_1286_ = lean_apply_1(v_x_1283_, v_x_1285_);
v___x_1287_ = lean_unbox_uint64(v___x_1286_);
lean_dec_ref(v___x_1286_);
v_h_1288_ = lean_uint64_to_usize(v___x_1287_);
v___x_1289_ = l_Lean_PersistentHashMap_eraseAux___redArg(v_x_1282_, v_x_1284_, v_h_1288_, v_x_1285_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase(lean_object* v_00_u03b1_1290_, lean_object* v_00_u03b2_1291_, lean_object* v_x_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_PersistentHashMap_erase___redArg(v_x_1292_, v_x_1293_, v_x_1294_, v_x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg(lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_f_1299_, lean_object* v_x_1300_, size_t v_x_1301_, size_t v_x_1302_, lean_object* v_x_1303_){
_start:
{
if (lean_obj_tag(v_x_1300_) == 0)
{
lean_object* v_es_1304_; size_t v___x_1305_; size_t v___x_1306_; lean_object* v_j_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_es_1304_ = lean_ctor_get(v_x_1300_, 0);
v___x_1305_ = ((size_t)31ULL);
v___x_1306_ = lean_usize_land(v_x_1301_, v___x_1305_);
v_j_1307_ = lean_usize_to_nat(v___x_1306_);
v___x_1308_ = lean_array_get_size(v_es_1304_);
v___x_1309_ = lean_nat_dec_lt(v_j_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_dec(v_j_1307_);
lean_dec(v_x_1303_);
lean_dec_ref(v_f_1299_);
lean_dec_ref(v_inst_1298_);
lean_dec_ref(v_inst_1297_);
return v_x_1300_;
}
else
{
lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1378_; 
lean_inc_ref(v_es_1304_);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_x_1300_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v_x_1300_, 0);
lean_dec(v_unused_1379_);
v___x_1311_ = v_x_1300_;
v_isShared_1312_ = v_isSharedCheck_1378_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v_x_1300_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1378_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_v_1313_; lean_object* v___x_1314_; lean_object* v_xs_x27_1315_; lean_object* v___y_1317_; 
v_v_1313_ = lean_array_fget(v_es_1304_, v_j_1307_);
v___x_1314_ = lean_box(0);
v_xs_x27_1315_ = lean_array_fset(v_es_1304_, v_j_1307_, v___x_1314_);
switch(lean_obj_tag(v_v_1313_))
{
case 0:
{
lean_object* v_key_1322_; lean_object* v_val_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
lean_dec_ref(v_inst_1298_);
v_key_1322_ = lean_ctor_get(v_v_1313_, 0);
v_val_1323_ = lean_ctor_get(v_v_1313_, 1);
lean_inc(v_key_1322_);
lean_inc(v_x_1303_);
v___x_1324_ = lean_apply_2(v_inst_1297_, v_x_1303_, v_key_1322_);
v___x_1325_ = lean_unbox(v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = lean_box(0);
v___x_1327_ = lean_apply_1(v_f_1299_, v___x_1326_);
if (lean_obj_tag(v___x_1327_) == 0)
{
lean_dec(v_x_1303_);
v___y_1317_ = v_v_1313_;
goto v___jp_1316_;
}
else
{
lean_object* v_val_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1336_; 
lean_inc(v_val_1323_);
lean_inc(v_key_1322_);
lean_dec_ref_known(v_v_1313_, 2);
v_val_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1336_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_val_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1336_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1322_, v_val_1323_, v_x_1303_, v_val_1328_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v___x_1332_);
v___x_1334_ = v___x_1330_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
v___y_1317_ = v___x_1334_;
goto v___jp_1316_;
}
}
}
}
else
{
lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1347_; 
lean_inc(v_val_1323_);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_v_1313_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; lean_object* v_unused_1349_; 
v_unused_1348_ = lean_ctor_get(v_v_1313_, 1);
lean_dec(v_unused_1348_);
v_unused_1349_ = lean_ctor_get(v_v_1313_, 0);
lean_dec(v_unused_1349_);
v___x_1338_ = v_v_1313_;
v_isShared_1339_ = v_isSharedCheck_1347_;
goto v_resetjp_1337_;
}
else
{
lean_dec(v_v_1313_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1347_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1340_, 0, v_val_1323_);
v___x_1341_ = lean_apply_1(v_f_1299_, v___x_1340_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v___x_1342_; 
lean_del_object(v___x_1338_);
lean_dec(v_x_1303_);
v___x_1342_ = lean_box(2);
v___y_1317_ = v___x_1342_;
goto v___jp_1316_;
}
else
{
lean_object* v_val_1343_; lean_object* v___x_1345_; 
v_val_1343_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_val_1343_);
lean_dec_ref_known(v___x_1341_, 1);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v_val_1343_);
lean_ctor_set(v___x_1338_, 0, v_x_1303_);
v___x_1345_ = v___x_1338_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_x_1303_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_val_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
v___y_1317_ = v___x_1345_;
goto v___jp_1316_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1373_; 
v_node_1350_ = lean_ctor_get(v_v_1313_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_v_1313_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1352_ = v_v_1313_;
v_isShared_1353_ = v_isSharedCheck_1373_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_node_1350_);
lean_dec(v_v_1313_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1373_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
size_t v___x_1354_; size_t v___x_1355_; size_t v___x_1356_; size_t v___x_1357_; lean_object* v_newNode_1358_; lean_object* v___x_1359_; 
v___x_1354_ = ((size_t)5ULL);
v___x_1355_ = lean_usize_shift_right(v_x_1301_, v___x_1354_);
v___x_1356_ = ((size_t)1ULL);
v___x_1357_ = lean_usize_add(v_x_1302_, v___x_1356_);
v_newNode_1358_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1297_, v_inst_1298_, v_f_1299_, v_node_1350_, v___x_1355_, v___x_1357_, v_x_1303_);
lean_inc_ref(v_newNode_1358_);
v___x_1359_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1358_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v___x_1361_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 0, v_newNode_1358_);
v___x_1361_ = v___x_1352_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_newNode_1358_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
v___y_1317_ = v___x_1361_;
goto v___jp_1316_;
}
}
else
{
lean_object* v_val_1363_; lean_object* v_fst_1364_; lean_object* v_snd_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_dec_ref(v_newNode_1358_);
lean_del_object(v___x_1352_);
v_val_1363_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_val_1363_);
lean_dec_ref_known(v___x_1359_, 1);
v_fst_1364_ = lean_ctor_get(v_val_1363_, 0);
v_snd_1365_ = lean_ctor_get(v_val_1363_, 1);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_val_1363_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v_val_1363_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_snd_1365_);
lean_inc(v_fst_1364_);
lean_dec(v_val_1363_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_fst_1364_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_snd_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
v___y_1317_ = v___x_1370_;
goto v___jp_1316_;
}
}
}
}
}
default: 
{
lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_dec_ref(v_inst_1298_);
lean_dec_ref(v_inst_1297_);
v___x_1374_ = lean_box(0);
v___x_1375_ = lean_apply_1(v_f_1299_, v___x_1374_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_dec(v_x_1303_);
v___y_1317_ = v_v_1313_;
goto v___jp_1316_;
}
else
{
lean_object* v_val_1376_; lean_object* v___x_1377_; 
v_val_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_val_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_x_1303_);
lean_ctor_set(v___x_1377_, 1, v_val_1376_);
v___y_1317_ = v___x_1377_;
goto v___jp_1316_;
}
}
}
v___jp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = lean_array_fset(v_xs_x27_1315_, v_j_1307_, v___y_1317_);
lean_dec(v_j_1307_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1318_);
v___x_1320_ = v___x_1311_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
else
{
lean_object* v_ks_1380_; lean_object* v_vs_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1414_; 
v_ks_1380_ = lean_ctor_get(v_x_1300_, 0);
v_vs_1381_ = lean_ctor_get(v_x_1300_, 1);
v_isSharedCheck_1414_ = !lean_is_exclusive(v_x_1300_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1383_ = v_x_1300_;
v_isShared_1384_ = v_isSharedCheck_1414_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_vs_1381_);
lean_inc(v_ks_1380_);
lean_dec(v_x_1300_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1414_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; 
lean_inc(v_x_1303_);
lean_inc_ref(v_inst_1297_);
v___x_1385_ = l_Array_finIdxOf_x3f___redArg(v_inst_1297_, v_ks_1380_, v_x_1303_);
if (lean_obj_tag(v___x_1385_) == 0)
{
lean_object* v___x_1387_; 
if (v_isShared_1384_ == 0)
{
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_ks_1380_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_vs_1381_);
v___x_1387_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_apply_1(v_f_1299_, v___x_1388_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_dec(v_x_1303_);
lean_dec_ref(v_inst_1298_);
lean_dec_ref(v_inst_1297_);
return v___x_1387_;
}
else
{
lean_object* v_val_1390_; lean_object* v___x_1391_; 
v_val_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_val_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = l_Lean_PersistentHashMap_insertAux___redArg(v_inst_1297_, v_inst_1298_, v___x_1387_, v_x_1301_, v_x_1302_, v_x_1303_, v_val_1390_);
return v___x_1391_;
}
}
}
else
{
lean_object* v_val_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1413_; 
lean_dec_ref(v_inst_1298_);
lean_dec_ref(v_inst_1297_);
v_val_1393_ = lean_ctor_get(v___x_1385_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1385_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1395_ = v___x_1385_;
v_isShared_1396_ = v_isSharedCheck_1413_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_val_1393_);
lean_dec(v___x_1385_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1413_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_v_x27_1397_; lean_object* v_keys_1398_; lean_object* v_vals_1399_; lean_object* v___x_1401_; 
v_v_x27_1397_ = lean_array_fget(v_vs_1381_, v_val_1393_);
lean_inc(v_val_1393_);
v_keys_1398_ = l_Array_eraseIdx___redArg(v_ks_1380_, v_val_1393_);
v_vals_1399_ = l_Array_eraseIdx___redArg(v_vs_1381_, v_val_1393_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v_v_x27_1397_);
v___x_1401_ = v___x_1395_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_v_x27_1397_);
v___x_1401_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_apply_1(v_f_1299_, v___x_1401_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v___x_1404_; 
lean_dec(v_x_1303_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v_vals_1399_);
lean_ctor_set(v___x_1383_, 0, v_keys_1398_);
v___x_1404_ = v___x_1383_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_keys_1398_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_vals_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
else
{
lean_object* v_val_1406_; lean_object* v_keys_1407_; lean_object* v_vals_1408_; lean_object* v___x_1410_; 
v_val_1406_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_val_1406_);
lean_dec_ref_known(v___x_1402_, 1);
v_keys_1407_ = lean_array_push(v_keys_1398_, v_x_1303_);
v_vals_1408_ = lean_array_push(v_vals_1399_, v_val_1406_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v_vals_1408_);
lean_ctor_set(v___x_1383_, 0, v_keys_1407_);
v___x_1410_ = v___x_1383_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_keys_1407_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_vals_1408_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___redArg___boxed(lean_object* v_inst_1415_, lean_object* v_inst_1416_, lean_object* v_f_1417_, lean_object* v_x_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_){
_start:
{
size_t v_x_413__boxed_1422_; size_t v_x_414__boxed_1423_; lean_object* v_res_1424_; 
v_x_413__boxed_1422_ = lean_unbox_usize(v_x_1419_);
lean_dec(v_x_1419_);
v_x_414__boxed_1423_ = lean_unbox_usize(v_x_1420_);
lean_dec(v_x_1420_);
v_res_1424_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1415_, v_inst_1416_, v_f_1417_, v_x_1418_, v_x_413__boxed_1422_, v_x_414__boxed_1423_, v_x_1421_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_inst_1427_, lean_object* v_inst_1428_, lean_object* v_f_1429_, lean_object* v_x_1430_, size_t v_x_1431_, size_t v_x_1432_, lean_object* v_x_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_PersistentHashMap_alterAux___redArg(v_inst_1427_, v_inst_1428_, v_f_1429_, v_x_1430_, v_x_1431_, v_x_1432_, v_x_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_00_u03b2_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_f_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_){
_start:
{
size_t v_x_635__boxed_1444_; size_t v_x_636__boxed_1445_; lean_object* v_res_1446_; 
v_x_635__boxed_1444_ = lean_unbox_usize(v_x_1441_);
lean_dec(v_x_1441_);
v_x_636__boxed_1445_ = lean_unbox_usize(v_x_1442_);
lean_dec(v_x_1442_);
v_res_1446_ = l_Lean_PersistentHashMap_alterAux(v_00_u03b1_1435_, v_00_u03b2_1436_, v_inst_1437_, v_inst_1438_, v_f_1439_, v_x_1440_, v_x_635__boxed_1444_, v_x_636__boxed_1445_, v_x_1443_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter___redArg(lean_object* v_x_1447_, lean_object* v_x_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_, lean_object* v_x_1451_){
_start:
{
lean_object* v___x_1452_; uint64_t v___x_1453_; size_t v_h_1454_; size_t v___x_1455_; lean_object* v___x_1456_; 
lean_inc_ref(v_x_1448_);
lean_inc(v_x_1450_);
v___x_1452_ = lean_apply_1(v_x_1448_, v_x_1450_);
v___x_1453_ = lean_unbox_uint64(v___x_1452_);
lean_dec_ref(v___x_1452_);
v_h_1454_ = lean_uint64_to_usize(v___x_1453_);
v___x_1455_ = ((size_t)1ULL);
v___x_1456_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1447_, v_x_1448_, v_x_1451_, v_x_1449_, v_h_1454_, v___x_1455_, v_x_1450_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alter(lean_object* v_00_u03b1_1457_, lean_object* v_00_u03b2_1458_, lean_object* v_x_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
lean_object* v___x_1464_; uint64_t v___x_1465_; size_t v_h_1466_; size_t v___x_1467_; lean_object* v___x_1468_; 
lean_inc_ref(v_x_1460_);
lean_inc(v_x_1462_);
v___x_1464_ = lean_apply_1(v_x_1460_, v_x_1462_);
v___x_1465_ = lean_unbox_uint64(v___x_1464_);
lean_dec_ref(v___x_1464_);
v_h_1466_ = lean_uint64_to_usize(v___x_1465_);
v___x_1467_ = ((size_t)1ULL);
v___x_1468_ = l_Lean_PersistentHashMap_alterAux___redArg(v_x_1459_, v_x_1460_, v_x_1463_, v_x_1461_, v_h_1466_, v___x_1467_, v_x_1462_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed(lean_object* v_i_1469_, lean_object* v_inst_1470_, lean_object* v_f_1471_, lean_object* v_keys_1472_, lean_object* v_vals_1473_, lean_object* v_____do__lift_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(v_i_1469_, v_inst_1470_, v_f_1471_, v_keys_1472_, v_vals_1473_, v_____do__lift_1474_);
lean_dec(v_i_1469_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(lean_object* v_inst_1476_, lean_object* v_f_1477_, lean_object* v_keys_1478_, lean_object* v_vals_1479_, lean_object* v_i_1480_, lean_object* v_acc_1481_){
_start:
{
lean_object* v_toApplicative_1482_; lean_object* v_toBind_1483_; lean_object* v_toPure_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_toApplicative_1482_ = lean_ctor_get(v_inst_1476_, 0);
v_toBind_1483_ = lean_ctor_get(v_inst_1476_, 1);
lean_inc(v_toBind_1483_);
v_toPure_1484_ = lean_ctor_get(v_toApplicative_1482_, 1);
v___x_1485_ = lean_array_get_size(v_keys_1478_);
v___x_1486_ = lean_nat_dec_lt(v_i_1480_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; 
lean_inc(v_toPure_1484_);
lean_dec(v_toBind_1483_);
lean_dec(v_i_1480_);
lean_dec_ref(v_vals_1479_);
lean_dec_ref(v_keys_1478_);
lean_dec(v_f_1477_);
lean_dec_ref(v_inst_1476_);
v___x_1487_ = lean_apply_2(v_toPure_1484_, lean_box(0), v_acc_1481_);
return v___x_1487_;
}
else
{
lean_object* v___f_1488_; lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
lean_inc_ref(v_vals_1479_);
lean_inc_ref(v_keys_1478_);
lean_inc(v_f_1477_);
lean_inc(v_i_1480_);
v___f_1488_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1488_, 0, v_i_1480_);
lean_closure_set(v___f_1488_, 1, v_inst_1476_);
lean_closure_set(v___f_1488_, 2, v_f_1477_);
lean_closure_set(v___f_1488_, 3, v_keys_1478_);
lean_closure_set(v___f_1488_, 4, v_vals_1479_);
v_k_1489_ = lean_array_fget(v_keys_1478_, v_i_1480_);
lean_dec_ref(v_keys_1478_);
v_v_1490_ = lean_array_fget(v_vals_1479_, v_i_1480_);
lean_dec(v_i_1480_);
lean_dec_ref(v_vals_1479_);
v___x_1491_ = lean_apply_3(v_f_1477_, v_acc_1481_, v_k_1489_, v_v_1490_);
v___x_1492_ = lean_apply_4(v_toBind_1483_, lean_box(0), lean_box(0), v___x_1491_, v___f_1488_);
return v___x_1492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg___lam__0(lean_object* v_i_1493_, lean_object* v_inst_1494_, lean_object* v_f_1495_, lean_object* v_keys_1496_, lean_object* v_vals_1497_, lean_object* v_____do__lift_1498_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1499_ = lean_unsigned_to_nat(1u);
v___x_1500_ = lean_nat_add(v_i_1493_, v___x_1499_);
v___x_1501_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1494_, v_f_1495_, v_keys_1496_, v_vals_1497_, v___x_1500_, v_____do__lift_1498_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse(lean_object* v_m_1502_, lean_object* v_inst_1503_, lean_object* v_00_u03c3_1504_, lean_object* v_00_u03b1_1505_, lean_object* v_00_u03b2_1506_, lean_object* v_f_1507_, lean_object* v_keys_1508_, lean_object* v_vals_1509_, lean_object* v_heq_1510_, lean_object* v_i_1511_, lean_object* v_acc_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1503_, v_f_1507_, v_keys_1508_, v_vals_1509_, v_i_1511_, v_acc_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object* v_inst_1514_, lean_object* v_f_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_){
_start:
{
if (lean_obj_tag(v_x_1516_) == 0)
{
lean_object* v_toApplicative_1518_; lean_object* v_toPure_1519_; lean_object* v_es_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_toApplicative_1518_ = lean_ctor_get(v_inst_1514_, 0);
v_toPure_1519_ = lean_ctor_get(v_toApplicative_1518_, 1);
v_es_1520_ = lean_ctor_get(v_x_1516_, 0);
lean_inc_ref(v_es_1520_);
lean_dec_ref_known(v_x_1516_, 1);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = lean_array_get_size(v_es_1520_);
v___x_1523_ = lean_nat_dec_lt(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; 
lean_inc(v_toPure_1519_);
lean_dec_ref(v_es_1520_);
lean_dec(v_f_1515_);
lean_dec_ref(v_inst_1514_);
v___x_1524_ = lean_apply_2(v_toPure_1519_, lean_box(0), v_x_1517_);
return v___x_1524_;
}
else
{
lean_object* v___f_1525_; uint8_t v___x_1526_; 
lean_inc(v_toPure_1519_);
lean_inc_ref(v_inst_1514_);
v___f_1525_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0), 5, 3);
lean_closure_set(v___f_1525_, 0, v_f_1515_);
lean_closure_set(v___f_1525_, 1, v_inst_1514_);
lean_closure_set(v___f_1525_, 2, v_toPure_1519_);
v___x_1526_ = lean_nat_dec_le(v___x_1522_, v___x_1522_);
if (v___x_1526_ == 0)
{
if (v___x_1523_ == 0)
{
lean_object* v___x_1527_; 
lean_inc(v_toPure_1519_);
lean_dec_ref(v___f_1525_);
lean_dec_ref(v_es_1520_);
lean_dec_ref(v_inst_1514_);
v___x_1527_ = lean_apply_2(v_toPure_1519_, lean_box(0), v_x_1517_);
return v___x_1527_;
}
else
{
size_t v___x_1528_; size_t v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = ((size_t)0ULL);
v___x_1529_ = lean_usize_of_nat(v___x_1522_);
v___x_1530_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1514_, v___f_1525_, v_es_1520_, v___x_1528_, v___x_1529_, v_x_1517_);
return v___x_1530_;
}
}
else
{
size_t v___x_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = ((size_t)0ULL);
v___x_1532_ = lean_usize_of_nat(v___x_1522_);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1514_, v___f_1525_, v_es_1520_, v___x_1531_, v___x_1532_, v_x_1517_);
return v___x_1533_;
}
}
}
else
{
lean_object* v_ks_1534_; lean_object* v_vs_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v_ks_1534_ = lean_ctor_get(v_x_1516_, 0);
lean_inc_ref(v_ks_1534_);
v_vs_1535_ = lean_ctor_get(v_x_1516_, 1);
lean_inc_ref(v_vs_1535_);
lean_dec_ref_known(v_x_1516_, 2);
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___redArg(v_inst_1514_, v_f_1515_, v_ks_1534_, v_vs_1535_, v___x_1536_, v_x_1517_);
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg___lam__0(lean_object* v_f_1538_, lean_object* v_inst_1539_, lean_object* v_toPure_1540_, lean_object* v_acc_1541_, lean_object* v_entry_1542_){
_start:
{
switch(lean_obj_tag(v_entry_1542_))
{
case 0:
{
lean_object* v_key_1543_; lean_object* v_val_1544_; lean_object* v___x_1545_; 
lean_dec(v_toPure_1540_);
lean_dec_ref(v_inst_1539_);
v_key_1543_ = lean_ctor_get(v_entry_1542_, 0);
lean_inc(v_key_1543_);
v_val_1544_ = lean_ctor_get(v_entry_1542_, 1);
lean_inc(v_val_1544_);
lean_dec_ref_known(v_entry_1542_, 2);
v___x_1545_ = lean_apply_3(v_f_1538_, v_acc_1541_, v_key_1543_, v_val_1544_);
return v___x_1545_;
}
case 1:
{
lean_object* v_node_1546_; lean_object* v___x_1547_; 
lean_dec(v_toPure_1540_);
v_node_1546_ = lean_ctor_get(v_entry_1542_, 0);
lean_inc(v_node_1546_);
lean_dec_ref_known(v_entry_1542_, 1);
v___x_1547_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1539_, v_f_1538_, v_node_1546_, v_acc_1541_);
return v___x_1547_;
}
default: 
{
lean_object* v___x_1548_; 
lean_dec_ref(v_inst_1539_);
lean_dec(v_f_1538_);
v___x_1548_ = lean_apply_2(v_toPure_1540_, lean_box(0), v_acc_1541_);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux(lean_object* v_m_1549_, lean_object* v_inst_1550_, lean_object* v_00_u03c3_1551_, lean_object* v_00_u03b1_1552_, lean_object* v_00_u03b2_1553_, lean_object* v_f_1554_, lean_object* v_x_1555_, lean_object* v_x_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1550_, v_f_1554_, v_x_1555_, v_x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___redArg(lean_object* v_inst_1558_, lean_object* v_map_1559_, lean_object* v_f_1560_, lean_object* v_init_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1558_, v_f_1560_, v_map_1559_, v_init_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM(lean_object* v_m_1563_, lean_object* v_inst_1564_, lean_object* v_00_u03c3_1565_, lean_object* v_00_u03b1_1566_, lean_object* v_00_u03b2_1567_, lean_object* v_x_1568_, lean_object* v_x_1569_, lean_object* v_map_1570_, lean_object* v_f_1571_, lean_object* v_init_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1564_, v_f_1571_, v_map_1570_, v_init_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___boxed(lean_object* v_m_1574_, lean_object* v_inst_1575_, lean_object* v_00_u03c3_1576_, lean_object* v_00_u03b1_1577_, lean_object* v_00_u03b2_1578_, lean_object* v_x_1579_, lean_object* v_x_1580_, lean_object* v_map_1581_, lean_object* v_f_1582_, lean_object* v_init_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Lean_PersistentHashMap_foldlM(v_m_1574_, v_inst_1575_, v_00_u03c3_1576_, v_00_u03b1_1577_, v_00_u03b2_1578_, v_x_1579_, v_x_1580_, v_map_1581_, v_f_1582_, v_init_1583_);
lean_dec_ref(v_x_1580_);
lean_dec_ref(v_x_1579_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg___lam__0(lean_object* v_f_1585_, lean_object* v_x_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = lean_apply_2(v_f_1585_, v___y_1587_, v___y_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___redArg(lean_object* v_inst_1590_, lean_object* v_map_1591_, lean_object* v_f_1592_){
_start:
{
lean_object* v___f_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___f_1593_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1593_, 0, v_f_1592_);
v___x_1594_ = lean_box(0);
v___x_1595_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_1590_, v___f_1593_, v_map_1591_, v___x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM(lean_object* v_m_1596_, lean_object* v_inst_1597_, lean_object* v_00_u03b1_1598_, lean_object* v_00_u03b2_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_, lean_object* v_map_1602_, lean_object* v_f_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_1597_, v_map_1602_, v_f_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___boxed(lean_object* v_m_1605_, lean_object* v_inst_1606_, lean_object* v_00_u03b1_1607_, lean_object* v_00_u03b2_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_, lean_object* v_map_1611_, lean_object* v_f_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_PersistentHashMap_forM(v_m_1605_, v_inst_1606_, v_00_u03b1_1607_, v_00_u03b2_1608_, v_x_1609_, v_x_1610_, v_map_1611_, v_f_1612_);
lean_dec_ref(v_x_1610_);
lean_dec_ref(v_x_1609_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg___lam__0(lean_object* v_f_1614_, lean_object* v_x1_1615_, lean_object* v_x2_1616_, lean_object* v_x3_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = lean_apply_3(v_f_1614_, v_x1_1615_, v_x2_1616_, v_x3_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object* v_map_1638_, lean_object* v_f_1639_, lean_object* v_init_1640_){
_start:
{
lean_object* v___f_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___f_1641_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1641_, 0, v_f_1639_);
v___x_1642_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1643_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1642_, v___f_1641_, v_map_1638_, v_init_1640_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl(lean_object* v_00_u03c3_1644_, lean_object* v_00_u03b1_1645_, lean_object* v_00_u03b2_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_, lean_object* v_map_1649_, lean_object* v_f_1650_, lean_object* v_init_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_1649_, v_f_1650_, v_init_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___boxed(lean_object* v_00_u03c3_1653_, lean_object* v_00_u03b1_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_, lean_object* v_map_1658_, lean_object* v_f_1659_, lean_object* v_init_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_PersistentHashMap_foldl(v_00_u03c3_1653_, v_00_u03b1_1654_, v_00_u03b2_1655_, v_x_1656_, v_x_1657_, v_map_1658_, v_f_1659_, v_init_1660_);
lean_dec_ref(v_x_1657_);
lean_dec_ref(v_x_1656_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit___redArg(lean_object* v_x_1662_, lean_object* v_x_1663_, lean_object* v_f_1664_, lean_object* v_old_1665_, lean_object* v_acc_1666_, lean_object* v_k_1667_, lean_object* v_v_1668_){
_start:
{
uint8_t v___x_1669_; 
lean_inc(v_k_1667_);
v___x_1669_ = l_Lean_PersistentHashMap_contains___redArg(v_x_1662_, v_x_1663_, v_old_1665_, v_k_1667_);
if (v___x_1669_ == 0)
{
lean_object* v___x_1670_; 
v___x_1670_ = lean_apply_3(v_f_1664_, v_acc_1666_, v_k_1667_, v_v_1668_);
return v___x_1670_;
}
else
{
lean_dec(v_v_1668_);
lean_dec(v_k_1667_);
lean_dec(v_f_1664_);
return v_acc_1666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit(lean_object* v_00_u03c3_1671_, lean_object* v_00_u03b1_1672_, lean_object* v_00_u03b2_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v_f_1676_, lean_object* v_old_1677_, lean_object* v_acc_1678_, lean_object* v_k_1679_, lean_object* v_v_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit___redArg(v_x_1674_, v_x_1675_, v_f_1676_, v_old_1677_, v_acc_1678_, v_k_1679_, v_v_1680_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg(lean_object* v_x_1682_, lean_object* v_x_1683_, lean_object* v_f_1684_, lean_object* v_old_1685_, lean_object* v_ks_1686_, lean_object* v_vs_1687_, lean_object* v_i_1688_, lean_object* v_acc_1689_){
_start:
{
lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = lean_array_get_size(v_ks_1686_);
v___x_1691_ = lean_nat_dec_lt(v_i_1688_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_dec(v_i_1688_);
lean_dec_ref(v_old_1685_);
lean_dec(v_f_1684_);
lean_dec_ref(v_x_1683_);
lean_dec_ref(v_x_1682_);
return v_acc_1689_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1692_ = lean_unsigned_to_nat(1u);
v___x_1693_ = lean_nat_add(v_i_1688_, v___x_1692_);
v___x_1694_ = lean_array_fget_borrowed(v_ks_1686_, v_i_1688_);
v___x_1695_ = lean_array_fget_borrowed(v_vs_1687_, v_i_1688_);
lean_dec(v_i_1688_);
lean_inc(v___x_1695_);
lean_inc(v___x_1694_);
lean_inc_ref(v_old_1685_);
lean_inc(v_f_1684_);
lean_inc_ref(v_x_1683_);
lean_inc_ref(v_x_1682_);
v___x_1696_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit___redArg(v_x_1682_, v_x_1683_, v_f_1684_, v_old_1685_, v_acc_1689_, v___x_1694_, v___x_1695_);
v_i_1688_ = v___x_1693_;
v_acc_1689_ = v___x_1696_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg___boxed(lean_object* v_x_1698_, lean_object* v_x_1699_, lean_object* v_f_1700_, lean_object* v_old_1701_, lean_object* v_ks_1702_, lean_object* v_vs_1703_, lean_object* v_i_1704_, lean_object* v_acc_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg(v_x_1698_, v_x_1699_, v_f_1700_, v_old_1701_, v_ks_1702_, v_vs_1703_, v_i_1704_, v_acc_1705_);
lean_dec_ref(v_vs_1703_);
lean_dec_ref(v_ks_1702_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision(lean_object* v_00_u03c3_1707_, lean_object* v_00_u03b1_1708_, lean_object* v_00_u03b2_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_, lean_object* v_f_1712_, lean_object* v_old_1713_, lean_object* v_ks_1714_, lean_object* v_vs_1715_, lean_object* v_h_1716_, lean_object* v_i_1717_, lean_object* v_acc_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg(v_x_1710_, v_x_1711_, v_f_1712_, v_old_1713_, v_ks_1714_, v_vs_1715_, v_i_1717_, v_acc_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___boxed(lean_object* v_00_u03c3_1720_, lean_object* v_00_u03b1_1721_, lean_object* v_00_u03b2_1722_, lean_object* v_x_1723_, lean_object* v_x_1724_, lean_object* v_f_1725_, lean_object* v_old_1726_, lean_object* v_ks_1727_, lean_object* v_vs_1728_, lean_object* v_h_1729_, lean_object* v_i_1730_, lean_object* v_acc_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision(v_00_u03c3_1720_, v_00_u03b1_1721_, v_00_u03b2_1722_, v_x_1723_, v_x_1724_, v_f_1725_, v_old_1726_, v_ks_1727_, v_vs_1728_, v_h_1729_, v_i_1730_, v_acc_1731_);
lean_dec_ref(v_vs_1728_);
lean_dec_ref(v_ks_1727_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(lean_object* v_x_1733_, lean_object* v_x_1734_, lean_object* v_f_1735_, lean_object* v_old_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_){
_start:
{
if (lean_obj_tag(v_a_1737_) == 0)
{
lean_object* v_es_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; uint8_t v___x_1743_; 
v_es_1739_ = lean_ctor_get(v_a_1737_, 0);
lean_inc_ref(v_es_1739_);
lean_dec_ref_known(v_a_1737_, 1);
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = lean_array_get_size(v_es_1739_);
v___x_1742_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_1743_ = lean_nat_dec_lt(v___x_1740_, v___x_1741_);
if (v___x_1743_ == 0)
{
lean_dec_ref(v_es_1739_);
lean_dec_ref(v_old_1736_);
lean_dec(v_f_1735_);
lean_dec_ref(v_x_1734_);
lean_dec_ref(v_x_1733_);
return v_a_1738_;
}
else
{
lean_object* v___f_1744_; uint8_t v___x_1745_; 
v___f_1744_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg___lam__0), 6, 4);
lean_closure_set(v___f_1744_, 0, v_x_1733_);
lean_closure_set(v___f_1744_, 1, v_x_1734_);
lean_closure_set(v___f_1744_, 2, v_f_1735_);
lean_closure_set(v___f_1744_, 3, v_old_1736_);
v___x_1745_ = lean_nat_dec_le(v___x_1741_, v___x_1741_);
if (v___x_1745_ == 0)
{
if (v___x_1743_ == 0)
{
lean_dec_ref(v___f_1744_);
lean_dec_ref(v_es_1739_);
return v_a_1738_;
}
else
{
size_t v___x_1746_; size_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1746_ = ((size_t)0ULL);
v___x_1747_ = lean_usize_of_nat(v___x_1741_);
v___x_1748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1742_, v___f_1744_, v_es_1739_, v___x_1746_, v___x_1747_, v_a_1738_);
return v___x_1748_;
}
}
else
{
size_t v___x_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = ((size_t)0ULL);
v___x_1750_ = lean_usize_of_nat(v___x_1741_);
v___x_1751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1742_, v___f_1744_, v_es_1739_, v___x_1749_, v___x_1750_, v_a_1738_);
return v___x_1751_;
}
}
}
else
{
lean_object* v_ks_1752_; lean_object* v_vs_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_ks_1752_ = lean_ctor_get(v_a_1737_, 0);
lean_inc_ref(v_ks_1752_);
v_vs_1753_ = lean_ctor_get(v_a_1737_, 1);
lean_inc_ref(v_vs_1753_);
lean_dec_ref_known(v_a_1737_, 2);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goCollision___redArg(v_x_1733_, v_x_1734_, v_f_1735_, v_old_1736_, v_ks_1752_, v_vs_1753_, v___x_1754_, v_a_1738_);
lean_dec_ref(v_vs_1753_);
lean_dec_ref(v_ks_1752_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg___lam__0(lean_object* v_x_1756_, lean_object* v_x_1757_, lean_object* v_f_1758_, lean_object* v_old_1759_, lean_object* v_x1_1760_, lean_object* v_x2_1761_){
_start:
{
switch(lean_obj_tag(v_x2_1761_))
{
case 0:
{
lean_object* v_key_1762_; lean_object* v_val_1763_; lean_object* v___x_1764_; 
v_key_1762_ = lean_ctor_get(v_x2_1761_, 0);
lean_inc(v_key_1762_);
v_val_1763_ = lean_ctor_get(v_x2_1761_, 1);
lean_inc(v_val_1763_);
lean_dec_ref_known(v_x2_1761_, 2);
v___x_1764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit___redArg(v_x_1756_, v_x_1757_, v_f_1758_, v_old_1759_, v_x1_1760_, v_key_1762_, v_val_1763_);
return v___x_1764_;
}
case 1:
{
lean_object* v_node_1765_; lean_object* v___x_1766_; 
v_node_1765_ = lean_ctor_get(v_x2_1761_, 0);
lean_inc(v_node_1765_);
lean_dec_ref_known(v_x2_1761_, 1);
v___x_1766_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(v_x_1756_, v_x_1757_, v_f_1758_, v_old_1759_, v_node_1765_, v_x1_1760_);
return v___x_1766_;
}
default: 
{
lean_dec_ref(v_old_1759_);
lean_dec(v_f_1758_);
lean_dec_ref(v_x_1757_);
lean_dec_ref(v_x_1756_);
return v_x1_1760_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll(lean_object* v_00_u03c3_1767_, lean_object* v_00_u03b1_1768_, lean_object* v_00_u03b2_1769_, lean_object* v_x_1770_, lean_object* v_x_1771_, lean_object* v_f_1772_, lean_object* v_old_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(v_x_1770_, v_x_1771_, v_f_1772_, v_old_1773_, v_a_1774_, v_a_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg(lean_object* v_x_1777_, lean_object* v_x_1778_, lean_object* v_f_1779_, lean_object* v_old_1780_, lean_object* v_nes_1781_, lean_object* v_oes_1782_, lean_object* v_i_1783_, lean_object* v_acc_1784_){
_start:
{
lean_object* v___y_1786_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_array_get_size(v_nes_1781_);
v___x_1791_ = lean_nat_dec_lt(v_i_1783_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_dec(v_i_1783_);
lean_dec_ref(v_old_1780_);
lean_dec(v_f_1779_);
lean_dec_ref(v_x_1778_);
lean_dec_ref(v_x_1777_);
return v_acc_1784_;
}
else
{
lean_object* v_ne_1792_; lean_object* v___y_1794_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v_ne_1792_ = lean_array_fget_borrowed(v_nes_1781_, v_i_1783_);
v___x_1806_ = lean_array_get_size(v_oes_1782_);
v___x_1807_ = lean_nat_dec_lt(v_i_1783_, v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_box(2);
v___y_1794_ = v___x_1808_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_array_fget_borrowed(v_oes_1782_, v_i_1783_);
v___y_1794_ = v___x_1809_;
goto v___jp_1793_;
}
v___jp_1793_:
{
size_t v___x_1795_; size_t v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = lean_ptr_addr(v_ne_1792_);
v___x_1796_ = lean_ptr_addr(v___y_1794_);
v___x_1797_ = lean_usize_dec_eq(v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
switch(lean_obj_tag(v_ne_1792_))
{
case 0:
{
lean_object* v_key_1798_; lean_object* v_val_1799_; lean_object* v___x_1800_; 
v_key_1798_ = lean_ctor_get(v_ne_1792_, 0);
v_val_1799_ = lean_ctor_get(v_ne_1792_, 1);
lean_inc(v_val_1799_);
lean_inc(v_key_1798_);
lean_inc_ref(v_old_1780_);
lean_inc(v_f_1779_);
lean_inc_ref(v_x_1778_);
lean_inc_ref(v_x_1777_);
v___x_1800_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_visit___redArg(v_x_1777_, v_x_1778_, v_f_1779_, v_old_1780_, v_acc_1784_, v_key_1798_, v_val_1799_);
v___y_1786_ = v___x_1800_;
goto v___jp_1785_;
}
case 1:
{
if (lean_obj_tag(v___y_1794_) == 1)
{
lean_object* v_node_1801_; lean_object* v_node_1802_; lean_object* v___x_1803_; 
v_node_1801_ = lean_ctor_get(v_ne_1792_, 0);
v_node_1802_ = lean_ctor_get(v___y_1794_, 0);
lean_inc(v_node_1801_);
lean_inc_ref(v_old_1780_);
lean_inc(v_f_1779_);
lean_inc_ref(v_x_1778_);
lean_inc_ref(v_x_1777_);
v___x_1803_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(v_x_1777_, v_x_1778_, v_f_1779_, v_old_1780_, v_node_1801_, v_node_1802_, v_acc_1784_);
v___y_1786_ = v___x_1803_;
goto v___jp_1785_;
}
else
{
lean_object* v_node_1804_; lean_object* v___x_1805_; 
v_node_1804_ = lean_ctor_get(v_ne_1792_, 0);
lean_inc(v_node_1804_);
lean_inc_ref(v_old_1780_);
lean_inc(v_f_1779_);
lean_inc_ref(v_x_1778_);
lean_inc_ref(v_x_1777_);
v___x_1805_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(v_x_1777_, v_x_1778_, v_f_1779_, v_old_1780_, v_node_1804_, v_acc_1784_);
v___y_1786_ = v___x_1805_;
goto v___jp_1785_;
}
}
default: 
{
v___y_1786_ = v_acc_1784_;
goto v___jp_1785_;
}
}
}
else
{
v___y_1786_ = v_acc_1784_;
goto v___jp_1785_;
}
}
}
v___jp_1785_:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = lean_unsigned_to_nat(1u);
v___x_1788_ = lean_nat_add(v_i_1783_, v___x_1787_);
lean_dec(v_i_1783_);
v_i_1783_ = v___x_1788_;
v_acc_1784_ = v___y_1786_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(lean_object* v_x_1810_, lean_object* v_x_1811_, lean_object* v_f_1812_, lean_object* v_old_1813_, lean_object* v_new_1814_, lean_object* v_old_1815_, lean_object* v_acc_1816_){
_start:
{
size_t v___x_1817_; size_t v___x_1818_; uint8_t v___x_1819_; 
v___x_1817_ = lean_ptr_addr(v_new_1814_);
v___x_1818_ = lean_ptr_addr(v_old_1815_);
v___x_1819_ = lean_usize_dec_eq(v___x_1817_, v___x_1818_);
if (v___x_1819_ == 0)
{
if (lean_obj_tag(v_new_1814_) == 0)
{
if (lean_obj_tag(v_old_1815_) == 0)
{
lean_object* v_es_1820_; lean_object* v_es_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_es_1820_ = lean_ctor_get(v_new_1814_, 0);
lean_inc_ref(v_es_1820_);
lean_dec_ref_known(v_new_1814_, 1);
v_es_1821_ = lean_ctor_get(v_old_1815_, 0);
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg(v_x_1810_, v_x_1811_, v_f_1812_, v_old_1813_, v_es_1820_, v_es_1821_, v___x_1822_, v_acc_1816_);
lean_dec_ref(v_es_1820_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; 
v___x_1824_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(v_x_1810_, v_x_1811_, v_f_1812_, v_old_1813_, v_new_1814_, v_acc_1816_);
return v___x_1824_;
}
}
else
{
lean_object* v___x_1825_; 
v___x_1825_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goAll___redArg(v_x_1810_, v_x_1811_, v_f_1812_, v_old_1813_, v_new_1814_, v_acc_1816_);
return v___x_1825_;
}
}
else
{
lean_dec_ref(v_new_1814_);
lean_dec_ref(v_old_1813_);
lean_dec(v_f_1812_);
lean_dec_ref(v_x_1811_);
lean_dec_ref(v_x_1810_);
return v_acc_1816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg___boxed(lean_object* v_x_1826_, lean_object* v_x_1827_, lean_object* v_f_1828_, lean_object* v_old_1829_, lean_object* v_new_1830_, lean_object* v_old_1831_, lean_object* v_acc_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(v_x_1826_, v_x_1827_, v_f_1828_, v_old_1829_, v_new_1830_, v_old_1831_, v_acc_1832_);
lean_dec_ref(v_old_1831_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg___boxed(lean_object* v_x_1834_, lean_object* v_x_1835_, lean_object* v_f_1836_, lean_object* v_old_1837_, lean_object* v_nes_1838_, lean_object* v_oes_1839_, lean_object* v_i_1840_, lean_object* v_acc_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg(v_x_1834_, v_x_1835_, v_f_1836_, v_old_1837_, v_nes_1838_, v_oes_1839_, v_i_1840_, v_acc_1841_);
lean_dec_ref(v_oes_1839_);
lean_dec_ref(v_nes_1838_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries(lean_object* v_00_u03c3_1843_, lean_object* v_00_u03b1_1844_, lean_object* v_00_u03b2_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_f_1848_, lean_object* v_old_1849_, lean_object* v_nes_1850_, lean_object* v_oes_1851_, lean_object* v_i_1852_, lean_object* v_acc_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___redArg(v_x_1846_, v_x_1847_, v_f_1848_, v_old_1849_, v_nes_1850_, v_oes_1851_, v_i_1852_, v_acc_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries___boxed(lean_object* v_00_u03c3_1855_, lean_object* v_00_u03b1_1856_, lean_object* v_00_u03b2_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_, lean_object* v_f_1860_, lean_object* v_old_1861_, lean_object* v_nes_1862_, lean_object* v_oes_1863_, lean_object* v_i_1864_, lean_object* v_acc_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_goEntries(v_00_u03c3_1855_, v_00_u03b1_1856_, v_00_u03b2_1857_, v_x_1858_, v_x_1859_, v_f_1860_, v_old_1861_, v_nes_1862_, v_oes_1863_, v_i_1864_, v_acc_1865_);
lean_dec_ref(v_oes_1863_);
lean_dec_ref(v_nes_1862_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go(lean_object* v_00_u03c3_1867_, lean_object* v_00_u03b1_1868_, lean_object* v_00_u03b2_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_, lean_object* v_f_1872_, lean_object* v_old_1873_, lean_object* v_new_1874_, lean_object* v_old_1875_, lean_object* v_acc_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(v_x_1870_, v_x_1871_, v_f_1872_, v_old_1873_, v_new_1874_, v_old_1875_, v_acc_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___boxed(lean_object* v_00_u03c3_1878_, lean_object* v_00_u03b1_1879_, lean_object* v_00_u03b2_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_, lean_object* v_f_1883_, lean_object* v_old_1884_, lean_object* v_new_1885_, lean_object* v_old_1886_, lean_object* v_acc_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go(v_00_u03c3_1878_, v_00_u03b1_1879_, v_00_u03b2_1880_, v_x_1881_, v_x_1882_, v_f_1883_, v_old_1884_, v_new_1885_, v_old_1886_, v_acc_1887_);
lean_dec_ref(v_old_1886_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe___redArg(lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_f_1891_, lean_object* v_new_1892_, lean_object* v_old_1893_, lean_object* v_init_1894_){
_start:
{
lean_object* v___x_1895_; 
lean_inc_ref(v_old_1893_);
v___x_1895_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(v_x_1889_, v_x_1890_, v_f_1891_, v_old_1893_, v_new_1892_, v_old_1893_, v_init_1894_);
lean_dec_ref(v_old_1893_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe(lean_object* v_00_u03c3_1896_, lean_object* v_00_u03b1_1897_, lean_object* v_00_u03b2_1898_, lean_object* v_x_1899_, lean_object* v_x_1900_, lean_object* v_f_1901_, lean_object* v_new_1902_, lean_object* v_old_1903_, lean_object* v_init_1904_){
_start:
{
lean_object* v___x_1905_; 
lean_inc_ref(v_old_1903_);
v___x_1905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlNewEntriesUnsafe_go___redArg(v_x_1899_, v_x_1900_, v_f_1901_, v_old_1903_, v_new_1902_, v_old_1903_, v_init_1904_);
lean_dec_ref(v_old_1903_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__0(lean_object* v_x_1906_){
_start:
{
if (lean_obj_tag(v_x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
v_a_1907_ = lean_ctor_get(v_x_1906_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_x_1906_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v_x_1906_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v_x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
v_a_1915_ = lean_ctor_get(v_x_1906_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_x_1906_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v_x_1906_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v_x_1906_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__1(lean_object* v_toPure_1923_, lean_object* v_result_1924_){
_start:
{
lean_object* v_a_1925_; lean_object* v___x_1926_; 
v_a_1925_ = lean_ctor_get(v_result_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v_result_1924_);
v___x_1926_ = lean_apply_2(v_toPure_1923_, lean_box(0), v_a_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___lam__2(lean_object* v_toFunctor_1927_, lean_object* v_f_1928_, lean_object* v_intoError_1929_, lean_object* v_s_1930_, lean_object* v_a_1931_, lean_object* v_b_1932_){
_start:
{
lean_object* v_map_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1942_; 
v_map_1933_ = lean_ctor_get(v_toFunctor_1927_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_toFunctor_1927_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v_toFunctor_1927_, 1);
lean_dec(v_unused_1943_);
v___x_1935_ = v_toFunctor_1927_;
v_isShared_1936_ = v_isSharedCheck_1942_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_map_1933_);
lean_dec(v_toFunctor_1927_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1942_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 1, v_b_1932_);
lean_ctor_set(v___x_1935_, 0, v_a_1931_);
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1931_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_b_1932_);
v___x_1938_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_apply_2(v_f_1928_, v___x_1938_, v_s_1930_);
v___x_1940_ = lean_apply_4(v_map_1933_, lean_box(0), lean_box(0), v_intoError_1929_, v___x_1939_);
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg(lean_object* v_inst_1945_, lean_object* v_map_1946_, lean_object* v_init_1947_, lean_object* v_f_1948_){
_start:
{
lean_object* v_toApplicative_1949_; lean_object* v_toBind_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___f_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v_toFunctor_1961_; lean_object* v_toPure_1962_; lean_object* v_intoError_1963_; lean_object* v___f_1964_; lean_object* v___f_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v_toApplicative_1949_ = lean_ctor_get(v_inst_1945_, 0);
lean_inc_ref(v_toApplicative_1949_);
v_toBind_1950_ = lean_ctor_get(v_inst_1945_, 1);
lean_inc(v_toBind_1950_);
lean_inc_ref_n(v_inst_1945_, 6);
v___f_1951_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1951_, 0, v_inst_1945_);
v___f_1952_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_1952_, 0, v_inst_1945_);
v___f_1953_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_1953_, 0, v_inst_1945_);
v___f_1954_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_1954_, 0, v_inst_1945_);
v___x_1955_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_1955_, 0, lean_box(0));
lean_closure_set(v___x_1955_, 1, lean_box(0));
lean_closure_set(v___x_1955_, 2, v_inst_1945_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
lean_ctor_set(v___x_1956_, 1, v___f_1951_);
v___x_1957_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_1957_, 0, lean_box(0));
lean_closure_set(v___x_1957_, 1, lean_box(0));
lean_closure_set(v___x_1957_, 2, v_inst_1945_);
v___x_1958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1956_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
lean_ctor_set(v___x_1958_, 2, v___f_1952_);
lean_ctor_set(v___x_1958_, 3, v___f_1953_);
lean_ctor_set(v___x_1958_, 4, v___f_1954_);
v___x_1959_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_1959_, 0, lean_box(0));
lean_closure_set(v___x_1959_, 1, lean_box(0));
lean_closure_set(v___x_1959_, 2, v_inst_1945_);
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v_toFunctor_1961_ = lean_ctor_get(v_toApplicative_1949_, 0);
lean_inc_ref(v_toFunctor_1961_);
v_toPure_1962_ = lean_ctor_get(v_toApplicative_1949_, 1);
lean_inc(v_toPure_1962_);
lean_dec_ref(v_toApplicative_1949_);
v_intoError_1963_ = ((lean_object*)(l_Lean_PersistentHashMap_forIn___redArg___closed__0));
v___f_1964_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1964_, 0, v_toPure_1962_);
v___f_1965_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___redArg___lam__2), 6, 3);
lean_closure_set(v___f_1965_, 0, v_toFunctor_1961_);
lean_closure_set(v___f_1965_, 1, v_f_1948_);
lean_closure_set(v___f_1965_, 2, v_intoError_1963_);
lean_inc_ref(v_map_1946_);
v___x_1966_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_1960_, v___f_1965_, v_map_1946_, v_init_1947_);
v___x_1967_ = lean_apply_4(v_toBind_1950_, lean_box(0), lean_box(0), v___x_1966_, v___f_1964_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___redArg___boxed(lean_object* v_inst_1968_, lean_object* v_map_1969_, lean_object* v_init_1970_, lean_object* v_f_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1968_, v_map_1969_, v_init_1970_, v_f_1971_);
lean_dec_ref(v_map_1969_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn(lean_object* v_m_1973_, lean_object* v_00_u03c3_1974_, lean_object* v_00_u03b1_1975_, lean_object* v_00_u03b2_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_, lean_object* v_inst_1979_, lean_object* v_map_1980_, lean_object* v_init_1981_, lean_object* v_f_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1979_, v_map_1980_, v_init_1981_, v_f_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___boxed(lean_object* v_m_1984_, lean_object* v_00_u03c3_1985_, lean_object* v_00_u03b1_1986_, lean_object* v_00_u03b2_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v_inst_1990_, lean_object* v_map_1991_, lean_object* v_init_1992_, lean_object* v_f_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_PersistentHashMap_forIn(v_m_1984_, v_00_u03c3_1985_, v_00_u03b1_1986_, v_00_u03b2_1987_, v_x_1988_, v_x_1989_, v_inst_1990_, v_map_1991_, v_init_1992_, v_f_1993_);
lean_dec_ref(v_map_1991_);
lean_dec_ref(v_x_1989_);
lean_dec_ref(v_x_1988_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_inst_1995_, lean_object* v_00_u03b2_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v___x_2000_; 
v___x_2000_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_1995_, v___y_1997_, v___y_1998_, v___y_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed(lean_object* v_inst_2001_, lean_object* v_00_u03b2_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0(v_inst_2001_, v_00_u03b2_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec_ref(v___y_2003_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___redArg(lean_object* v_inst_2007_){
_start:
{
lean_object* v___f_2008_; 
v___f_2008_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2008_, 0, v_inst_2007_);
return v___f_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad(lean_object* v_m_2009_, lean_object* v_00_u03b1_2010_, lean_object* v_00_u03b2_2011_, lean_object* v_x_2012_, lean_object* v_x_2013_, lean_object* v_inst_2014_){
_start:
{
lean_object* v___f_2015_; 
v___f_2015_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_instForInProdOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2015_, 0, v_inst_2014_);
return v___f_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_instForInProdOfMonad___boxed(lean_object* v_m_2016_, lean_object* v_00_u03b1_2017_, lean_object* v_00_u03b2_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_, lean_object* v_inst_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_PersistentHashMap_instForInProdOfMonad(v_m_2016_, v_00_u03b1_2017_, v_00_u03b2_2018_, v_x_2019_, v_x_2020_, v_inst_2021_);
lean_dec_ref(v_x_2020_);
lean_dec_ref(v_x_2019_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__0(lean_object* v_toPure_2023_, lean_object* v_entries_x27_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v_entries_x27_2024_);
v___x_2026_ = lean_apply_2(v_toPure_2023_, lean_box(0), v___x_2025_);
return v___x_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__1(lean_object* v_toPure_2027_, lean_object* v_____do__lift_2028_){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2029_, 0, v_____do__lift_2028_);
v___x_2030_ = lean_apply_2(v_toPure_2027_, lean_box(0), v___x_2029_);
return v___x_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__2(lean_object* v_key_2031_, lean_object* v_toPure_2032_, lean_object* v_____do__lift_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v_key_2031_);
lean_ctor_set(v___x_2034_, 1, v_____do__lift_2033_);
v___x_2035_ = lean_apply_2(v_toPure_2032_, lean_box(0), v___x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__4(lean_object* v_ks_2036_, lean_object* v_toPure_2037_, lean_object* v_____x_2038_){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2039_, 0, v_ks_2036_);
lean_ctor_set(v___x_2039_, 1, v_____x_2038_);
v___x_2040_ = lean_apply_2(v_toPure_2037_, lean_box(0), v___x_2039_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg(lean_object* v_inst_2041_, lean_object* v_f_2042_, lean_object* v_n_2043_){
_start:
{
if (lean_obj_tag(v_n_2043_) == 0)
{
lean_object* v_toApplicative_2044_; lean_object* v_toBind_2045_; lean_object* v_toPure_2046_; lean_object* v_es_2047_; lean_object* v___f_2048_; lean_object* v___f_2049_; lean_object* v___f_2050_; size_t v_sz_2051_; size_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_toApplicative_2044_ = lean_ctor_get(v_inst_2041_, 0);
v_toBind_2045_ = lean_ctor_get(v_inst_2041_, 1);
lean_inc_n(v_toBind_2045_, 2);
v_toPure_2046_ = lean_ctor_get(v_toApplicative_2044_, 1);
v_es_2047_ = lean_ctor_get(v_n_2043_, 0);
lean_inc_ref(v_es_2047_);
lean_dec_ref_known(v_n_2043_, 1);
lean_inc_n(v_toPure_2046_, 3);
v___f_2048_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2048_, 0, v_toPure_2046_);
v___f_2049_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2049_, 0, v_toPure_2046_);
lean_inc_ref(v_inst_2041_);
v___f_2050_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__3), 6, 5);
lean_closure_set(v___f_2050_, 0, v_toPure_2046_);
lean_closure_set(v___f_2050_, 1, v_f_2042_);
lean_closure_set(v___f_2050_, 2, v_toBind_2045_);
lean_closure_set(v___f_2050_, 3, v_inst_2041_);
lean_closure_set(v___f_2050_, 4, v___f_2049_);
v_sz_2051_ = lean_array_size(v_es_2047_);
v___x_2052_ = ((size_t)0ULL);
v___x_2053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2041_, v___f_2050_, v_sz_2051_, v___x_2052_, v_es_2047_);
v___x_2054_ = lean_apply_4(v_toBind_2045_, lean_box(0), lean_box(0), v___x_2053_, v___f_2048_);
return v___x_2054_;
}
else
{
lean_object* v_toApplicative_2055_; lean_object* v_toBind_2056_; lean_object* v_toPure_2057_; lean_object* v_ks_2058_; lean_object* v_vs_2059_; lean_object* v___f_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_toApplicative_2055_ = lean_ctor_get(v_inst_2041_, 0);
v_toBind_2056_ = lean_ctor_get(v_inst_2041_, 1);
lean_inc(v_toBind_2056_);
v_toPure_2057_ = lean_ctor_get(v_toApplicative_2055_, 1);
v_ks_2058_ = lean_ctor_get(v_n_2043_, 0);
lean_inc_ref(v_ks_2058_);
v_vs_2059_ = lean_ctor_get(v_n_2043_, 1);
lean_inc_ref(v_vs_2059_);
lean_dec_ref_known(v_n_2043_, 2);
lean_inc(v_toPure_2057_);
v___f_2060_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__4), 3, 2);
lean_closure_set(v___f_2060_, 0, v_ks_2058_);
lean_closure_set(v___f_2060_, 1, v_toPure_2057_);
v___x_2061_ = l_Array_mapM_x27___redArg(v_inst_2041_, v_f_2042_, v_vs_2059_);
v___x_2062_ = lean_apply_4(v_toBind_2056_, lean_box(0), lean_box(0), v___x_2061_, v___f_2060_);
return v___x_2062_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux___redArg___lam__3(lean_object* v_toPure_2063_, lean_object* v_f_2064_, lean_object* v_toBind_2065_, lean_object* v_inst_2066_, lean_object* v___f_2067_, lean_object* v_x_2068_){
_start:
{
switch(lean_obj_tag(v_x_2068_))
{
case 0:
{
lean_object* v_key_2069_; lean_object* v_val_2070_; lean_object* v___f_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
lean_dec(v___f_2067_);
lean_dec_ref(v_inst_2066_);
v_key_2069_ = lean_ctor_get(v_x_2068_, 0);
lean_inc(v_key_2069_);
v_val_2070_ = lean_ctor_get(v_x_2068_, 1);
lean_inc(v_val_2070_);
lean_dec_ref_known(v_x_2068_, 2);
v___f_2071_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapMAux___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2071_, 0, v_key_2069_);
lean_closure_set(v___f_2071_, 1, v_toPure_2063_);
v___x_2072_ = lean_apply_1(v_f_2064_, v_val_2070_);
v___x_2073_ = lean_apply_4(v_toBind_2065_, lean_box(0), lean_box(0), v___x_2072_, v___f_2071_);
return v___x_2073_;
}
case 1:
{
lean_object* v_node_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_dec(v_toPure_2063_);
v_node_2074_ = lean_ctor_get(v_x_2068_, 0);
lean_inc(v_node_2074_);
lean_dec_ref_known(v_x_2068_, 1);
v___x_2075_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_2066_, v_f_2064_, v_node_2074_);
v___x_2076_ = lean_apply_4(v_toBind_2065_, lean_box(0), lean_box(0), v___x_2075_, v___f_2067_);
return v___x_2076_;
}
default: 
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec(v___f_2067_);
lean_dec_ref(v_inst_2066_);
lean_dec(v_toBind_2065_);
lean_dec(v_f_2064_);
v___x_2077_ = lean_box(2);
v___x_2078_ = lean_apply_2(v_toPure_2063_, lean_box(0), v___x_2077_);
return v___x_2078_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapMAux(lean_object* v_00_u03b1_2079_, lean_object* v_00_u03b2_2080_, lean_object* v_00_u03c3_2081_, lean_object* v_m_2082_, lean_object* v_inst_2083_, lean_object* v_f_2084_, lean_object* v_n_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_2083_, v_f_2084_, v_n_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg___lam__0(lean_object* v_toPure_2087_, lean_object* v_root_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_apply_2(v_toPure_2087_, lean_box(0), v_root_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___redArg(lean_object* v_inst_2090_, lean_object* v_pm_2091_, lean_object* v_f_2092_){
_start:
{
lean_object* v_toApplicative_2093_; lean_object* v_toBind_2094_; lean_object* v_toPure_2095_; lean_object* v___x_2096_; lean_object* v___f_2097_; lean_object* v___x_2098_; 
v_toApplicative_2093_ = lean_ctor_get(v_inst_2090_, 0);
v_toBind_2094_ = lean_ctor_get(v_inst_2090_, 1);
lean_inc(v_toBind_2094_);
v_toPure_2095_ = lean_ctor_get(v_toApplicative_2093_, 1);
lean_inc(v_toPure_2095_);
v___x_2096_ = l_Lean_PersistentHashMap_mapMAux___redArg(v_inst_2090_, v_f_2092_, v_pm_2091_);
v___f_2097_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_mapM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2097_, 0, v_toPure_2095_);
v___x_2098_ = lean_apply_4(v_toBind_2094_, lean_box(0), lean_box(0), v___x_2096_, v___f_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM(lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_00_u03c3_2101_, lean_object* v_m_2102_, lean_object* v_inst_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_, lean_object* v_pm_2106_, lean_object* v_f_2107_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Lean_PersistentHashMap_mapM___redArg(v_inst_2103_, v_pm_2106_, v_f_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_mapM___boxed(lean_object* v_00_u03b1_2109_, lean_object* v_00_u03b2_2110_, lean_object* v_00_u03c3_2111_, lean_object* v_m_2112_, lean_object* v_inst_2113_, lean_object* v_x_2114_, lean_object* v_x_2115_, lean_object* v_pm_2116_, lean_object* v_f_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_PersistentHashMap_mapM(v_00_u03b1_2109_, v_00_u03b2_2110_, v_00_u03c3_2111_, v_m_2112_, v_inst_2113_, v_x_2114_, v_x_2115_, v_pm_2116_, v_f_2117_);
lean_dec_ref(v_x_2115_);
lean_dec_ref(v_x_2114_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg___lam__0(lean_object* v_f_2119_, lean_object* v_x_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_apply_1(v_f_2119_, v_x_2120_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___redArg(lean_object* v_pm_2122_, lean_object* v_f_2123_){
_start:
{
lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___f_2124_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2124_, 0, v_f_2123_);
v___x_2125_ = ((lean_object*)(l_Lean_PersistentHashMap_foldl___redArg___closed__9));
v___x_2126_ = l_Lean_PersistentHashMap_mapM___redArg(v___x_2125_, v_pm_2122_, v___f_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map(lean_object* v_00_u03b1_2127_, lean_object* v_00_u03b2_2128_, lean_object* v_00_u03c3_2129_, lean_object* v_x_2130_, lean_object* v_x_2131_, lean_object* v_pm_2132_, lean_object* v_f_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_PersistentHashMap_map___redArg(v_pm_2132_, v_f_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_map___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_00_u03b2_2136_, lean_object* v_00_u03c3_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_, lean_object* v_pm_2140_, lean_object* v_f_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_PersistentHashMap_map(v_00_u03b1_2135_, v_00_u03b2_2136_, v_00_u03c3_2137_, v_x_2138_, v_x_2139_, v_pm_2140_, v_f_2141_);
lean_dec_ref(v_x_2139_);
lean_dec_ref(v_x_2138_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg___lam__0(lean_object* v_ps_2143_, lean_object* v_k_2144_, lean_object* v_v_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2146_, 0, v_k_2144_);
lean_ctor_set(v___x_2146_, 1, v_v_2145_);
v___x_2147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v_ps_2143_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___redArg(lean_object* v_m_2149_){
_start:
{
lean_object* v___f_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___f_2150_ = ((lean_object*)(l_Lean_PersistentHashMap_toList___redArg___closed__0));
v___x_2151_ = lean_box(0);
v___x_2152_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_2149_, v___f_2150_, v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList(lean_object* v_00_u03b1_2153_, lean_object* v_00_u03b2_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v_m_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Lean_PersistentHashMap_toList___redArg(v_m_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toList___boxed(lean_object* v_00_u03b1_2159_, lean_object* v_00_u03b2_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_, lean_object* v_m_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_PersistentHashMap_toList(v_00_u03b1_2159_, v_00_u03b2_2160_, v_x_2161_, v_x_2162_, v_m_2163_);
lean_dec_ref(v_x_2162_);
lean_dec_ref(v_x_2161_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg___lam__0(lean_object* v_ps_2165_, lean_object* v_k_2166_, lean_object* v_v_2167_){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2168_, 0, v_k_2166_);
lean_ctor_set(v___x_2168_, 1, v_v_2167_);
v___x_2169_ = lean_array_push(v_ps_2165_, v___x_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___redArg(lean_object* v_m_2173_){
_start:
{
lean_object* v___f_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___f_2174_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__0));
v___x_2175_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___redArg___closed__1));
v___x_2176_ = l_Lean_PersistentHashMap_foldl___redArg(v_m_2173_, v___f_2174_, v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray(lean_object* v_00_u03b1_2177_, lean_object* v_00_u03b2_2178_, lean_object* v_x_2179_, lean_object* v_x_2180_, lean_object* v_m_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_PersistentHashMap_toArray___redArg(v_m_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___boxed(lean_object* v_00_u03b1_2183_, lean_object* v_00_u03b2_2184_, lean_object* v_x_2185_, lean_object* v_x_2186_, lean_object* v_m_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_PersistentHashMap_toArray(v_00_u03b1_2183_, v_00_u03b2_2184_, v_x_2185_, v_x_2186_, v_m_2187_);
lean_dec_ref(v_x_2186_);
lean_dec_ref(v_x_2185_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg(lean_object* v_x_2189_, lean_object* v_x_2190_, lean_object* v_x_2191_){
_start:
{
if (lean_obj_tag(v_x_2189_) == 0)
{
lean_object* v_es_2192_; lean_object* v_numNodes_2193_; lean_object* v_numNull_2194_; lean_object* v_numCollisions_2195_; lean_object* v_maxDepth_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2218_; 
v_es_2192_ = lean_ctor_get(v_x_2189_, 0);
v_numNodes_2193_ = lean_ctor_get(v_x_2190_, 0);
v_numNull_2194_ = lean_ctor_get(v_x_2190_, 1);
v_numCollisions_2195_ = lean_ctor_get(v_x_2190_, 2);
v_maxDepth_2196_ = lean_ctor_get(v_x_2190_, 3);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_x_2190_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2198_ = v_x_2190_;
v_isShared_2199_ = v_isSharedCheck_2218_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_maxDepth_2196_);
lean_inc(v_numCollisions_2195_);
lean_inc(v_numNull_2194_);
lean_inc(v_numNodes_2193_);
lean_dec(v_x_2190_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2218_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___y_2203_; uint8_t v___x_2217_; 
v___x_2200_ = lean_unsigned_to_nat(1u);
v___x_2201_ = lean_nat_add(v_numNodes_2193_, v___x_2200_);
lean_dec(v_numNodes_2193_);
v___x_2217_ = lean_nat_dec_le(v_maxDepth_2196_, v_x_2191_);
if (v___x_2217_ == 0)
{
v___y_2203_ = v_maxDepth_2196_;
goto v___jp_2202_;
}
else
{
lean_dec(v_maxDepth_2196_);
lean_inc(v_x_2191_);
v___y_2203_ = v_x_2191_;
goto v___jp_2202_;
}
v___jp_2202_:
{
lean_object* v_stats_2205_; 
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 3, v___y_2203_);
lean_ctor_set(v___x_2198_, 0, v___x_2201_);
v_stats_2205_ = v___x_2198_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v_numNull_2194_);
lean_ctor_set(v_reuseFailAlloc_2216_, 2, v_numCollisions_2195_);
lean_ctor_set(v_reuseFailAlloc_2216_, 3, v___y_2203_);
v_stats_2205_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v___x_2206_ = lean_unsigned_to_nat(0u);
v___x_2207_ = lean_array_get_size(v_es_2192_);
v___x_2208_ = lean_nat_dec_lt(v___x_2206_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_dec(v_x_2191_);
return v_stats_2205_;
}
else
{
uint8_t v___x_2209_; 
v___x_2209_ = lean_nat_dec_le(v___x_2207_, v___x_2207_);
if (v___x_2209_ == 0)
{
if (v___x_2208_ == 0)
{
lean_dec(v_x_2191_);
return v_stats_2205_;
}
else
{
size_t v___x_2210_; size_t v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = ((size_t)0ULL);
v___x_2211_ = lean_usize_of_nat(v___x_2207_);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2191_, v_es_2192_, v___x_2210_, v___x_2211_, v_stats_2205_);
lean_dec(v_x_2191_);
return v___x_2212_;
}
}
else
{
size_t v___x_2213_; size_t v___x_2214_; lean_object* v___x_2215_; 
v___x_2213_ = ((size_t)0ULL);
v___x_2214_ = lean_usize_of_nat(v___x_2207_);
v___x_2215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2191_, v_es_2192_, v___x_2213_, v___x_2214_, v_stats_2205_);
lean_dec(v_x_2191_);
return v___x_2215_;
}
}
}
}
}
}
else
{
lean_object* v_ks_2219_; lean_object* v_numNodes_2220_; lean_object* v_numNull_2221_; lean_object* v_numCollisions_2222_; lean_object* v_maxDepth_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2239_; 
v_ks_2219_ = lean_ctor_get(v_x_2189_, 0);
v_numNodes_2220_ = lean_ctor_get(v_x_2190_, 0);
v_numNull_2221_ = lean_ctor_get(v_x_2190_, 1);
v_numCollisions_2222_ = lean_ctor_get(v_x_2190_, 2);
v_maxDepth_2223_ = lean_ctor_get(v_x_2190_, 3);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_x_2190_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2225_ = v_x_2190_;
v_isShared_2226_ = v_isSharedCheck_2239_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_maxDepth_2223_);
lean_inc(v_numCollisions_2222_);
lean_inc(v_numNull_2221_);
lean_inc(v_numNodes_2220_);
lean_dec(v_x_2190_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2239_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v___x_2227_ = lean_unsigned_to_nat(1u);
v___x_2228_ = lean_nat_add(v_numNodes_2220_, v___x_2227_);
lean_dec(v_numNodes_2220_);
v___x_2229_ = lean_array_get_size(v_ks_2219_);
v___x_2230_ = lean_nat_add(v_numCollisions_2222_, v___x_2229_);
lean_dec(v_numCollisions_2222_);
v___x_2231_ = lean_nat_sub(v___x_2230_, v___x_2227_);
lean_dec(v___x_2230_);
v___x_2232_ = lean_nat_dec_le(v_maxDepth_2223_, v_x_2191_);
if (v___x_2232_ == 0)
{
lean_object* v___x_2234_; 
lean_dec(v_x_2191_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 2, v___x_2231_);
lean_ctor_set(v___x_2225_, 0, v___x_2228_);
v___x_2234_ = v___x_2225_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_numNull_2221_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_maxDepth_2223_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
else
{
lean_object* v___x_2237_; 
lean_dec(v_maxDepth_2223_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 3, v_x_2191_);
lean_ctor_set(v___x_2225_, 2, v___x_2231_);
lean_ctor_set(v___x_2225_, 0, v___x_2228_);
v___x_2237_ = v___x_2225_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_numNull_2221_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_x_2191_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(lean_object* v_x_2240_, lean_object* v_as_2241_, size_t v_i_2242_, size_t v_stop_2243_, lean_object* v_b_2244_){
_start:
{
lean_object* v___y_2246_; uint8_t v___x_2250_; 
v___x_2250_ = lean_usize_dec_eq(v_i_2242_, v_stop_2243_);
if (v___x_2250_ == 0)
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2252_ = lean_array_uget_borrowed(v_as_2241_, v_i_2242_);
switch(lean_obj_tag(v___x_2252_))
{
case 0:
{
v___y_2246_ = v_b_2244_;
goto v___jp_2245_;
}
case 1:
{
lean_object* v_node_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_node_2253_ = lean_ctor_get(v___x_2252_, 0);
v___x_2254_ = lean_nat_add(v_x_2240_, v___x_2251_);
v___x_2255_ = l_Lean_PersistentHashMap_collectStats___redArg(v_node_2253_, v_b_2244_, v___x_2254_);
v___y_2246_ = v___x_2255_;
goto v___jp_2245_;
}
default: 
{
lean_object* v_numNodes_2256_; lean_object* v_numNull_2257_; lean_object* v_numCollisions_2258_; lean_object* v_maxDepth_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2267_; 
v_numNodes_2256_ = lean_ctor_get(v_b_2244_, 0);
v_numNull_2257_ = lean_ctor_get(v_b_2244_, 1);
v_numCollisions_2258_ = lean_ctor_get(v_b_2244_, 2);
v_maxDepth_2259_ = lean_ctor_get(v_b_2244_, 3);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_b_2244_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2261_ = v_b_2244_;
v_isShared_2262_ = v_isSharedCheck_2267_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_maxDepth_2259_);
lean_inc(v_numCollisions_2258_);
lean_inc(v_numNull_2257_);
lean_inc(v_numNodes_2256_);
lean_dec(v_b_2244_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2267_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2263_; lean_object* v___x_2265_; 
v___x_2263_ = lean_nat_add(v_numNull_2257_, v___x_2251_);
lean_dec(v_numNull_2257_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 1, v___x_2263_);
v___x_2265_ = v___x_2261_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_numNodes_2256_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v_numCollisions_2258_);
lean_ctor_set(v_reuseFailAlloc_2266_, 3, v_maxDepth_2259_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
v___y_2246_ = v___x_2265_;
goto v___jp_2245_;
}
}
}
}
}
else
{
return v_b_2244_;
}
v___jp_2245_:
{
size_t v___x_2247_; size_t v___x_2248_; 
v___x_2247_ = ((size_t)1ULL);
v___x_2248_ = lean_usize_add(v_i_2242_, v___x_2247_);
v_i_2242_ = v___x_2248_;
v_b_2244_ = v___y_2246_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg___boxed(lean_object* v_x_2268_, lean_object* v_as_2269_, lean_object* v_i_2270_, lean_object* v_stop_2271_, lean_object* v_b_2272_){
_start:
{
size_t v_i_boxed_2273_; size_t v_stop_boxed_2274_; lean_object* v_res_2275_; 
v_i_boxed_2273_ = lean_unbox_usize(v_i_2270_);
lean_dec(v_i_2270_);
v_stop_boxed_2274_ = lean_unbox_usize(v_stop_2271_);
lean_dec(v_stop_2271_);
v_res_2275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2268_, v_as_2269_, v_i_boxed_2273_, v_stop_boxed_2274_, v_b_2272_);
lean_dec_ref(v_as_2269_);
lean_dec(v_x_2268_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___redArg___boxed(lean_object* v_x_2276_, lean_object* v_x_2277_, lean_object* v_x_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2276_, v_x_2277_, v_x_2278_);
lean_dec_ref(v_x_2276_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats(lean_object* v_00_u03b1_2280_, lean_object* v_00_u03b2_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_, lean_object* v_x_2284_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_PersistentHashMap_collectStats___redArg(v_x_2282_, v_x_2283_, v_x_2284_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_collectStats___boxed(lean_object* v_00_u03b1_2286_, lean_object* v_00_u03b2_2287_, lean_object* v_x_2288_, lean_object* v_x_2289_, lean_object* v_x_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_PersistentHashMap_collectStats(v_00_u03b1_2286_, v_00_u03b2_2287_, v_x_2288_, v_x_2289_, v_x_2290_);
lean_dec_ref(v_x_2288_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(lean_object* v_00_u03b1_2292_, lean_object* v_00_u03b2_2293_, lean_object* v_x_2294_, lean_object* v_as_2295_, size_t v_i_2296_, size_t v_stop_2297_, lean_object* v_b_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___redArg(v_x_2294_, v_as_2295_, v_i_2296_, v_stop_2297_, v_b_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2300_, lean_object* v_00_u03b2_2301_, lean_object* v_x_2302_, lean_object* v_as_2303_, lean_object* v_i_2304_, lean_object* v_stop_2305_, lean_object* v_b_2306_){
_start:
{
size_t v_i_boxed_2307_; size_t v_stop_boxed_2308_; lean_object* v_res_2309_; 
v_i_boxed_2307_ = lean_unbox_usize(v_i_2304_);
lean_dec(v_i_2304_);
v_stop_boxed_2308_ = lean_unbox_usize(v_stop_2305_);
lean_dec(v_stop_2305_);
v_res_2309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_collectStats_spec__0(v_00_u03b1_2300_, v_00_u03b2_2301_, v_x_2302_, v_as_2303_, v_i_boxed_2307_, v_stop_boxed_2308_, v_b_2306_);
lean_dec_ref(v_as_2303_);
lean_dec(v_x_2302_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg(lean_object* v_m_2312_){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2313_ = ((lean_object*)(l_Lean_PersistentHashMap_stats___redArg___closed__0));
v___x_2314_ = lean_unsigned_to_nat(1u);
v___x_2315_ = l_Lean_PersistentHashMap_collectStats___redArg(v_m_2312_, v___x_2313_, v___x_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___redArg___boxed(lean_object* v_m_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2316_);
lean_dec_ref(v_m_2316_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats(lean_object* v_00_u03b1_2318_, lean_object* v_00_u03b2_2319_, lean_object* v_x_2320_, lean_object* v_x_2321_, lean_object* v_m_2322_){
_start:
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_PersistentHashMap_stats___redArg(v_m_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_stats___boxed(lean_object* v_00_u03b1_2324_, lean_object* v_00_u03b2_2325_, lean_object* v_x_2326_, lean_object* v_x_2327_, lean_object* v_m_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_PersistentHashMap_stats(v_00_u03b1_2324_, v_00_u03b2_2325_, v_x_2326_, v_x_2327_, v_m_2328_);
lean_dec_ref(v_m_2328_);
lean_dec_ref(v_x_2327_);
lean_dec_ref(v_x_2326_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_Stats_toString(lean_object* v_s_2335_){
_start:
{
lean_object* v_numNodes_2336_; lean_object* v_numNull_2337_; lean_object* v_numCollisions_2338_; lean_object* v_maxDepth_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_numNodes_2336_ = lean_ctor_get(v_s_2335_, 0);
lean_inc(v_numNodes_2336_);
v_numNull_2337_ = lean_ctor_get(v_s_2335_, 1);
lean_inc(v_numNull_2337_);
v_numCollisions_2338_ = lean_ctor_get(v_s_2335_, 2);
lean_inc(v_numCollisions_2338_);
v_maxDepth_2339_ = lean_ctor_get(v_s_2335_, 3);
lean_inc(v_maxDepth_2339_);
lean_dec_ref(v_s_2335_);
v___x_2340_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__0));
v___x_2341_ = l_Nat_reprFast(v_numNodes_2336_);
v___x_2342_ = lean_string_append(v___x_2340_, v___x_2341_);
lean_dec_ref(v___x_2341_);
v___x_2343_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__1));
v___x_2344_ = lean_string_append(v___x_2342_, v___x_2343_);
v___x_2345_ = l_Nat_reprFast(v_numNull_2337_);
v___x_2346_ = lean_string_append(v___x_2344_, v___x_2345_);
lean_dec_ref(v___x_2345_);
v___x_2347_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__2));
v___x_2348_ = lean_string_append(v___x_2346_, v___x_2347_);
v___x_2349_ = l_Nat_reprFast(v_numCollisions_2338_);
v___x_2350_ = lean_string_append(v___x_2348_, v___x_2349_);
lean_dec_ref(v___x_2349_);
v___x_2351_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__3));
v___x_2352_ = lean_string_append(v___x_2350_, v___x_2351_);
v___x_2353_ = l_Nat_reprFast(v_maxDepth_2339_);
v___x_2354_ = lean_string_append(v___x_2352_, v___x_2353_);
lean_dec_ref(v___x_2353_);
v___x_2355_ = ((lean_object*)(l_Lean_PersistentHashMap_Stats_toString___closed__4));
v___x_2356_ = lean_string_append(v___x_2354_, v___x_2355_);
return v___x_2356_;
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
