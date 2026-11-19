// Lean compiler output
// Module: Lean.Data.PersistentArray
// Imports: public import Init.Data.Nat.Fold public import Init.Data.UInt.Basic import Init.Data.String.Defs import Init.Data.ToString.Macro import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_node_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedPersistentArrayNode_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedPersistentArrayNode_default___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedPersistentArrayNode_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedPersistentArrayNode_default___redArg___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedPersistentArrayNode_default___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedPersistentArrayNode_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArrayNode_isNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArrayNode_isNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_PersistentArray_initShift;
LEAN_EXPORT size_t l_Lean_PersistentArray_branching;
static lean_once_cell_t l_Lean_instInhabitedPersistentArray_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedPersistentArray_default___redArg___closed__0;
static lean_once_cell_t l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedPersistentArray_default___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedPersistentArray_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedPersistentArray_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentArray_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_empty___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentArray_mkEmptyArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_mkEmptyArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray(lean_object*);
LEAN_EXPORT size_t l_Lean_PersistentArray_mul2Shift(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mul2Shift___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_PersistentArray_div2Shift(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_div2Shift___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_PersistentArray_mod2Shift(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mod2Shift___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___redArg(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_PersistentArray_mkNewTail___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentArray_mkNewTail___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentArray_mkNewTail___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentArray_tooBig___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_tooBig___closed__0;
static lean_once_cell_t l_Lean_PersistentArray_tooBig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_tooBig___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_tooBig;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_rightpad_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_rightpad_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_rightpad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_rightpad___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_rightpad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_rightpad___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_object*);
static lean_once_cell_t l_Lean_PersistentArray_popLeaf___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_popLeaf___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_PersistentArray_findSomeMAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentArray_findSomeMAux___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentArray_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_foldl___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__0_value;
static const lean_closure_object l_Lean_PersistentArray_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_foldl___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__1_value;
static const lean_closure_object l_Lean_PersistentArray_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_foldl___redArg___closed__2 = (const lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__2_value;
static const lean_closure_object l_Lean_PersistentArray_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_foldl___redArg___closed__3 = (const lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__3_value;
static const lean_closure_object l_Lean_PersistentArray_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_foldl___redArg___closed__4 = (const lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__4_value;
static const lean_closure_object l_Lean_PersistentArray_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_foldl___redArg___closed__5 = (const lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__5_value;
static const lean_closure_object l_Lean_PersistentArray_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_foldl___redArg___closed__6 = (const lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__6_value;
static const lean_ctor_object l_Lean_PersistentArray_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__0_value),((lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__1_value)}};
static const lean_object* l_Lean_PersistentArray_foldl___redArg___closed__7 = (const lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__7_value;
static const lean_ctor_object l_Lean_PersistentArray_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__7_value),((lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__2_value),((lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__3_value),((lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__4_value),((lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__5_value)}};
static const lean_object* l_Lean_PersistentArray_foldl___redArg___closed__8 = (const lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__8_value;
static const lean_ctor_object l_Lean_PersistentArray_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__8_value),((lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__6_value)}};
static const lean_object* l_Lean_PersistentArray_foldl___redArg___closed__9 = (const lean_object*)&l_Lean_PersistentArray_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentArray_instAppend___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentArray_append___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_PersistentArray_instAppend___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentArray_instAppend___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__2(lean_object*);
static const lean_closure_object l_Lean_PersistentArray_mapMAux___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentArray_mapMAux___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_mapMAux___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentArray_mapMAux___redArg___closed__0_value;
static const lean_closure_object l_Lean_PersistentArray_mapMAux___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentArray_mapMAux___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_mapMAux___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentArray_mapMAux___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_PersistentArray_Stats_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "{nodes := "};
static const lean_object* l_Lean_PersistentArray_Stats_toString___closed__0 = (const lean_object*)&l_Lean_PersistentArray_Stats_toString___closed__0_value;
static const lean_string_object l_Lean_PersistentArray_Stats_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ", depth := "};
static const lean_object* l_Lean_PersistentArray_Stats_toString___closed__1 = (const lean_object*)&l_Lean_PersistentArray_Stats_toString___closed__1_value;
static const lean_string_object l_Lean_PersistentArray_Stats_toString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ", tail size := "};
static const lean_object* l_Lean_PersistentArray_Stats_toString___closed__2 = (const lean_object*)&l_Lean_PersistentArray_Stats_toString___closed__2_value;
static const lean_string_object l_Lean_PersistentArray_Stats_toString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_PersistentArray_Stats_toString___closed__3 = (const lean_object*)&l_Lean_PersistentArray_Stats_toString___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Stats_toString(lean_object*);
static const lean_closure_object l_Lean_PersistentArray_instToStringStats___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentArray_Stats_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentArray_instToStringStats___closed__0 = (const lean_object*)&l_Lean_PersistentArray_instToStringStats___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_PersistentArray_instToStringStats = (const lean_object*)&l_Lean_PersistentArray_instToStringStats___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_PersistentArrayNode_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___impl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_PersistentArrayNode_ctorIdx___impl(v_00_u03b1_8_, v_x_9_);
lean_dec_ref(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
lean_object* v_cs_13_; lean_object* v___x_14_; 
v_cs_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc_ref(v_cs_13_);
lean_dec_ref(v_t_11_);
v___x_14_ = lean_apply_1(v_k_12_, v_cs_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim(lean_object* v_00_u03b1_15_, lean_object* v_motive__1_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_18_, v_k_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim___boxed(lean_object* v_00_u03b1_22_, lean_object* v_motive__1_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_PersistentArrayNode_ctorElim(v_00_u03b1_22_, v_motive__1_23_, v_ctorIdx_24_, v_t_25_, v_h_26_, v_k_27_);
lean_dec(v_ctorIdx_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_node_elim___redArg(lean_object* v_t_29_, lean_object* v_node_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_29_, v_node_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_node_elim(lean_object* v_00_u03b1_32_, lean_object* v_motive__1_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_node_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_34_, v_node_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_leaf_elim___redArg(lean_object* v_t_38_, lean_object* v_leaf_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_38_, v_leaf_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_leaf_elim(lean_object* v_00_u03b1_41_, lean_object* v_motive__1_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_leaf_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_43_, v_leaf_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg(){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = ((lean_object*)(l_Lean_instInhabitedPersistentArrayNode_default___redArg___closed__1));
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg___boxed(lean_object* v___dummy_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v_res_54_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0(void){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object* v_00_u03b1_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode___redArg(){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode___redArg___boxed(lean_object* v___dummy_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_instInhabitedPersistentArrayNode___redArg();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object* v_a_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArrayNode_isNode___redArg(lean_object* v_x_64_){
_start:
{
if (lean_obj_tag(v_x_64_) == 0)
{
uint8_t v___x_65_; 
v___x_65_ = 1;
return v___x_65_;
}
else
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___redArg___boxed(lean_object* v_x_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_67_);
lean_dec_ref(v_x_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArrayNode_isNode(lean_object* v_00_u03b1_70_, lean_object* v_x_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___boxed(lean_object* v_00_u03b1_73_, lean_object* v_x_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lean_PersistentArrayNode_isNode(v_00_u03b1_73_, v_x_74_);
lean_dec_ref(v_x_74_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
static size_t _init_l_Lean_PersistentArray_initShift(void){
_start:
{
size_t v___x_77_; 
v___x_77_ = ((size_t)5ULL);
return v___x_77_;
}
}
static size_t _init_l_Lean_PersistentArray_branching(void){
_start:
{
size_t v___x_78_; 
v___x_78_ = ((size_t)32ULL);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_unsigned_to_nat(32u);
v___x_80_ = lean_mk_empty_array_with_capacity(v___x_79_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1(void){
_start:
{
size_t v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_82_ = ((size_t)5ULL);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_unsigned_to_nat(32u);
v___x_85_ = lean_mk_empty_array_with_capacity(v___x_84_);
v___x_86_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__0, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__0);
v___x_87_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_85_);
lean_ctor_set(v___x_87_, 2, v___x_83_);
lean_ctor_set(v___x_87_, 3, v___x_83_);
lean_ctor_set_usize(v___x_87_, 4, v___x_82_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default___redArg(){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default___redArg___boxed(lean_object* v___dummy_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v_res_91_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___closed__0(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object* v_00_u03b1_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__0, &l_Lean_instInhabitedPersistentArray_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__0);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray___redArg(){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__0, &l_Lean_instInhabitedPersistentArray_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__0);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray___redArg___boxed(lean_object* v___dummy_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_instInhabitedPersistentArray___redArg();
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray(lean_object* v_a_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__0, &l_Lean_instInhabitedPersistentArray_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__0);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty___redArg(){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_unsigned_to_nat(32u);
v___x_103_ = lean_mk_empty_array_with_capacity(v___x_102_);
lean_dec_ref(v___x_103_);
v___x_104_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty___redArg___boxed(lean_object* v___dummy_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_PersistentArray_empty___redArg();
return v_res_106_;
}
}
static lean_object* _init_l_Lean_PersistentArray_empty___closed__0(void){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_PersistentArray_empty___redArg();
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty(lean_object* v_00_u03b1_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
return v___x_109_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object* v_a_110_){
_start:
{
lean_object* v_size_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_size_111_ = lean_ctor_get(v_a_110_, 2);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_nat_dec_eq(v_size_111_, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___redArg___boxed(lean_object* v_a_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_114_);
lean_dec_ref(v_a_114_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty(lean_object* v_00_u03b1_117_, lean_object* v_a_118_){
_start:
{
uint8_t v___x_119_; 
v___x_119_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___boxed(lean_object* v_00_u03b1_120_, lean_object* v_a_121_){
_start:
{
uint8_t v_res_122_; lean_object* v_r_123_; 
v_res_122_ = l_Lean_PersistentArray_isEmpty(v_00_u03b1_120_, v_a_121_);
lean_dec_ref(v_a_121_);
v_r_123_ = lean_box(v_res_122_);
return v_r_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray___redArg(){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(32u);
v___x_126_ = lean_mk_empty_array_with_capacity(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray___redArg___boxed(lean_object* v___dummy_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_PersistentArray_mkEmptyArray___redArg();
return v_res_128_;
}
}
static lean_object* _init_l_Lean_PersistentArray_mkEmptyArray___closed__0(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_PersistentArray_mkEmptyArray___redArg();
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray(lean_object* v_00_u03b1_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
return v___x_131_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_mul2Shift(size_t v_i_132_, size_t v_shift_133_){
_start:
{
size_t v___x_134_; 
v___x_134_ = lean_usize_shift_left(v_i_132_, v_shift_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mul2Shift___boxed(lean_object* v_i_135_, lean_object* v_shift_136_){
_start:
{
size_t v_i_boxed_137_; size_t v_shift_boxed_138_; size_t v_res_139_; lean_object* v_r_140_; 
v_i_boxed_137_ = lean_unbox_usize(v_i_135_);
lean_dec(v_i_135_);
v_shift_boxed_138_ = lean_unbox_usize(v_shift_136_);
lean_dec(v_shift_136_);
v_res_139_ = l_Lean_PersistentArray_mul2Shift(v_i_boxed_137_, v_shift_boxed_138_);
v_r_140_ = lean_box_usize(v_res_139_);
return v_r_140_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_div2Shift(size_t v_i_141_, size_t v_shift_142_){
_start:
{
size_t v___x_143_; 
v___x_143_ = lean_usize_shift_right(v_i_141_, v_shift_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_div2Shift___boxed(lean_object* v_i_144_, lean_object* v_shift_145_){
_start:
{
size_t v_i_boxed_146_; size_t v_shift_boxed_147_; size_t v_res_148_; lean_object* v_r_149_; 
v_i_boxed_146_ = lean_unbox_usize(v_i_144_);
lean_dec(v_i_144_);
v_shift_boxed_147_ = lean_unbox_usize(v_shift_145_);
lean_dec(v_shift_145_);
v_res_148_ = l_Lean_PersistentArray_div2Shift(v_i_boxed_146_, v_shift_boxed_147_);
v_r_149_ = lean_box_usize(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_mod2Shift(size_t v_i_150_, size_t v_shift_151_){
_start:
{
size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v___x_155_; 
v___x_152_ = ((size_t)1ULL);
v___x_153_ = lean_usize_shift_left(v___x_152_, v_shift_151_);
v___x_154_ = lean_usize_sub(v___x_153_, v___x_152_);
v___x_155_ = lean_usize_land(v_i_150_, v___x_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mod2Shift___boxed(lean_object* v_i_156_, lean_object* v_shift_157_){
_start:
{
size_t v_i_boxed_158_; size_t v_shift_boxed_159_; size_t v_res_160_; lean_object* v_r_161_; 
v_i_boxed_158_ = lean_unbox_usize(v_i_156_);
lean_dec(v_i_156_);
v_shift_boxed_159_ = lean_unbox_usize(v_shift_157_);
lean_dec(v_shift_157_);
v_res_160_ = l_Lean_PersistentArray_mod2Shift(v_i_boxed_158_, v_shift_boxed_159_);
v_r_161_ = lean_box_usize(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___redArg(lean_object* v_inst_162_, lean_object* v_x_163_, size_t v_x_164_, size_t v_x_165_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
lean_object* v_cs_166_; lean_object* v___x_167_; size_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; size_t v___x_171_; size_t v___x_172_; size_t v___x_173_; size_t v___x_174_; size_t v___x_175_; size_t v___x_176_; 
v_cs_166_ = lean_ctor_get(v_x_163_, 0);
v___x_167_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_168_ = lean_usize_shift_right(v_x_164_, v_x_165_);
v___x_169_ = lean_usize_to_nat(v___x_168_);
v___x_170_ = lean_array_get_borrowed(v___x_167_, v_cs_166_, v___x_169_);
lean_dec(v___x_169_);
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_shift_left(v___x_171_, v_x_165_);
v___x_173_ = lean_usize_sub(v___x_172_, v___x_171_);
v___x_174_ = lean_usize_land(v_x_164_, v___x_173_);
v___x_175_ = ((size_t)5ULL);
v___x_176_ = lean_usize_sub(v_x_165_, v___x_175_);
v_x_163_ = v___x_170_;
v_x_164_ = v___x_174_;
v_x_165_ = v___x_176_;
goto _start;
}
else
{
lean_object* v_vs_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_vs_178_ = lean_ctor_get(v_x_163_, 0);
v___x_179_ = lean_usize_to_nat(v_x_164_);
v___x_180_ = lean_array_get_borrowed(v_inst_162_, v_vs_178_, v___x_179_);
lean_dec(v___x_179_);
lean_inc(v___x_180_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___redArg___boxed(lean_object* v_inst_181_, lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_x_184_){
_start:
{
size_t v_x_94__boxed_185_; size_t v_x_95__boxed_186_; lean_object* v_res_187_; 
v_x_94__boxed_185_ = lean_unbox_usize(v_x_183_);
lean_dec(v_x_183_);
v_x_95__boxed_186_ = lean_unbox_usize(v_x_184_);
lean_dec(v_x_184_);
v_res_187_ = l_Lean_PersistentArray_getAux___redArg(v_inst_181_, v_x_182_, v_x_94__boxed_185_, v_x_95__boxed_186_);
lean_dec_ref(v_x_182_);
lean_dec(v_inst_181_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux(lean_object* v_00_u03b1_188_, lean_object* v_inst_189_, lean_object* v_x_190_, size_t v_x_191_, size_t v_x_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_PersistentArray_getAux___redArg(v_inst_189_, v_x_190_, v_x_191_, v_x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___boxed(lean_object* v_00_u03b1_194_, lean_object* v_inst_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
size_t v_x_136__boxed_199_; size_t v_x_137__boxed_200_; lean_object* v_res_201_; 
v_x_136__boxed_199_ = lean_unbox_usize(v_x_197_);
lean_dec(v_x_197_);
v_x_137__boxed_200_ = lean_unbox_usize(v_x_198_);
lean_dec(v_x_198_);
v_res_201_ = l_Lean_PersistentArray_getAux(v_00_u03b1_194_, v_inst_195_, v_x_196_, v_x_136__boxed_199_, v_x_137__boxed_200_);
lean_dec_ref(v_x_196_);
lean_dec(v_inst_195_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object* v_inst_202_, lean_object* v_t_203_, lean_object* v_i_204_){
_start:
{
lean_object* v_root_205_; lean_object* v_tail_206_; size_t v_shift_207_; lean_object* v_tailOff_208_; uint8_t v___x_209_; 
v_root_205_ = lean_ctor_get(v_t_203_, 0);
v_tail_206_ = lean_ctor_get(v_t_203_, 1);
v_shift_207_ = lean_ctor_get_usize(v_t_203_, 4);
v_tailOff_208_ = lean_ctor_get(v_t_203_, 3);
v___x_209_ = lean_nat_dec_le(v_tailOff_208_, v_i_204_);
if (v___x_209_ == 0)
{
size_t v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_usize_of_nat(v_i_204_);
v___x_211_ = l_Lean_PersistentArray_getAux___redArg(v_inst_202_, v_root_205_, v___x_210_, v_shift_207_);
return v___x_211_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_nat_sub(v_i_204_, v_tailOff_208_);
v___x_213_ = lean_array_get_borrowed(v_inst_202_, v_tail_206_, v___x_212_);
lean_dec(v___x_212_);
lean_inc(v___x_213_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg___boxed(lean_object* v_inst_214_, lean_object* v_t_215_, lean_object* v_i_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_214_, v_t_215_, v_i_216_);
lean_dec(v_i_216_);
lean_dec_ref(v_t_215_);
lean_dec(v_inst_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21(lean_object* v_00_u03b1_218_, lean_object* v_inst_219_, lean_object* v_t_220_, lean_object* v_i_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_219_, v_t_220_, v_i_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___boxed(lean_object* v_00_u03b1_223_, lean_object* v_inst_224_, lean_object* v_t_225_, lean_object* v_i_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_PersistentArray_get_x21(v_00_u03b1_223_, v_inst_224_, v_t_225_, v_i_226_);
lean_dec(v_i_226_);
lean_dec_ref(v_t_225_);
lean_dec(v_inst_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(lean_object* v_inst_228_, lean_object* v_xs_229_, lean_object* v_i_230_, lean_object* v_x_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_228_, v_xs_229_, v_i_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed(lean_object* v_inst_233_, lean_object* v_xs_234_, lean_object* v_i_235_, lean_object* v_x_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(v_inst_233_, v_xs_234_, v_i_235_, v_x_236_);
lean_dec(v_i_235_);
lean_dec_ref(v_xs_234_);
lean_dec(v_inst_233_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg(lean_object* v_inst_238_){
_start:
{
lean_object* v___f_239_; 
v___f_239_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_239_, 0, v_inst_238_);
return v___f_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited(lean_object* v_00_u03b1_240_, lean_object* v_inst_241_){
_start:
{
lean_object* v___f_242_; 
v___f_242_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_242_, 0, v_inst_241_);
return v___f_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___redArg(lean_object* v_x_243_, size_t v_x_244_, size_t v_x_245_, lean_object* v_x_246_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v_cs_247_; size_t v_j_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v_cs_247_ = lean_ctor_get(v_x_243_, 0);
v_j_248_ = lean_usize_shift_right(v_x_244_, v_x_245_);
v___x_249_ = lean_usize_to_nat(v_j_248_);
v___x_250_ = lean_array_get_size(v_cs_247_);
v___x_251_ = lean_nat_dec_lt(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec(v___x_249_);
lean_dec(v_x_246_);
return v_x_243_;
}
else
{
lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_269_; 
lean_inc_ref(v_cs_247_);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_243_);
if (v_isSharedCheck_269_ == 0)
{
lean_object* v_unused_270_; 
v_unused_270_ = lean_ctor_get(v_x_243_, 0);
lean_dec(v_unused_270_);
v___x_253_ = v_x_243_;
v_isShared_254_ = v_isSharedCheck_269_;
goto v_resetjp_252_;
}
else
{
lean_dec(v_x_243_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_269_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v_i_258_; size_t v___x_259_; size_t v_shift_260_; lean_object* v_v_261_; lean_object* v___x_262_; lean_object* v_xs_x27_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_shift_left(v___x_255_, v_x_245_);
v___x_257_ = lean_usize_sub(v___x_256_, v___x_255_);
v_i_258_ = lean_usize_land(v_x_244_, v___x_257_);
v___x_259_ = ((size_t)5ULL);
v_shift_260_ = lean_usize_sub(v_x_245_, v___x_259_);
v_v_261_ = lean_array_fget(v_cs_247_, v___x_249_);
v___x_262_ = lean_box(0);
v_xs_x27_263_ = lean_array_fset(v_cs_247_, v___x_249_, v___x_262_);
v___x_264_ = l_Lean_PersistentArray_setAux___redArg(v_v_261_, v_i_258_, v_shift_260_, v_x_246_);
v___x_265_ = lean_array_fset(v_xs_x27_263_, v___x_249_, v___x_264_);
lean_dec(v___x_249_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v___x_265_);
v___x_267_ = v___x_253_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v_vs_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_280_; 
v_vs_271_ = lean_ctor_get(v_x_243_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v_x_243_);
if (v_isSharedCheck_280_ == 0)
{
v___x_273_ = v_x_243_;
v_isShared_274_ = v_isSharedCheck_280_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_vs_271_);
lean_dec(v_x_243_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_280_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_275_ = lean_usize_to_nat(v_x_244_);
v___x_276_ = lean_array_set(v_vs_271_, v___x_275_, v_x_246_);
lean_dec(v___x_275_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_276_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___redArg___boxed(lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
size_t v_x_79__boxed_285_; size_t v_x_80__boxed_286_; lean_object* v_res_287_; 
v_x_79__boxed_285_ = lean_unbox_usize(v_x_282_);
lean_dec(v_x_282_);
v_x_80__boxed_286_ = lean_unbox_usize(v_x_283_);
lean_dec(v_x_283_);
v_res_287_ = l_Lean_PersistentArray_setAux___redArg(v_x_281_, v_x_79__boxed_285_, v_x_80__boxed_286_, v_x_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux(lean_object* v_00_u03b1_288_, lean_object* v_x_289_, size_t v_x_290_, size_t v_x_291_, lean_object* v_x_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Lean_PersistentArray_setAux___redArg(v_x_289_, v_x_290_, v_x_291_, v_x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___boxed(lean_object* v_00_u03b1_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
size_t v_x_149__boxed_299_; size_t v_x_150__boxed_300_; lean_object* v_res_301_; 
v_x_149__boxed_299_ = lean_unbox_usize(v_x_296_);
lean_dec(v_x_296_);
v_x_150__boxed_300_ = lean_unbox_usize(v_x_297_);
lean_dec(v_x_297_);
v_res_301_ = l_Lean_PersistentArray_setAux(v_00_u03b1_294_, v_x_295_, v_x_149__boxed_299_, v_x_150__boxed_300_, v_x_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg(lean_object* v_t_302_, lean_object* v_i_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_root_305_; lean_object* v_tail_306_; lean_object* v_size_307_; size_t v_shift_308_; lean_object* v_tailOff_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_324_; 
v_root_305_ = lean_ctor_get(v_t_302_, 0);
v_tail_306_ = lean_ctor_get(v_t_302_, 1);
v_size_307_ = lean_ctor_get(v_t_302_, 2);
v_shift_308_ = lean_ctor_get_usize(v_t_302_, 4);
v_tailOff_309_ = lean_ctor_get(v_t_302_, 3);
v_isSharedCheck_324_ = !lean_is_exclusive(v_t_302_);
if (v_isSharedCheck_324_ == 0)
{
v___x_311_ = v_t_302_;
v_isShared_312_ = v_isSharedCheck_324_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_tailOff_309_);
lean_inc(v_size_307_);
lean_inc(v_tail_306_);
lean_inc(v_root_305_);
lean_dec(v_t_302_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_324_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
uint8_t v___x_313_; 
v___x_313_ = lean_nat_dec_le(v_tailOff_309_, v_i_303_);
if (v___x_313_ == 0)
{
size_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v___x_314_ = lean_usize_of_nat(v_i_303_);
v___x_315_ = l_Lean_PersistentArray_setAux___redArg(v_root_305_, v___x_314_, v_shift_308_, v_a_304_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 0, v___x_315_);
v___x_317_ = v___x_311_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_tail_306_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_size_307_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_tailOff_309_);
lean_ctor_set_usize(v_reuseFailAlloc_318_, 4, v_shift_308_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_319_ = lean_nat_sub(v_i_303_, v_tailOff_309_);
v___x_320_ = lean_array_set(v_tail_306_, v___x_319_, v_a_304_);
lean_dec(v___x_319_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_320_);
v___x_322_ = v___x_311_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_root_305_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_323_, 2, v_size_307_);
lean_ctor_set(v_reuseFailAlloc_323_, 3, v_tailOff_309_);
lean_ctor_set_usize(v_reuseFailAlloc_323_, 4, v_shift_308_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg___boxed(lean_object* v_t_325_, lean_object* v_i_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_PersistentArray_set___redArg(v_t_325_, v_i_326_, v_a_327_);
lean_dec(v_i_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set(lean_object* v_00_u03b1_329_, lean_object* v_t_330_, lean_object* v_i_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_PersistentArray_set___redArg(v_t_330_, v_i_331_, v_a_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___boxed(lean_object* v_00_u03b1_334_, lean_object* v_t_335_, lean_object* v_i_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_PersistentArray_set(v_00_u03b1_334_, v_t_335_, v_i_336_, v_a_337_);
lean_dec(v_i_336_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___redArg(lean_object* v_f_339_, lean_object* v_x_340_, size_t v_x_341_, size_t v_x_342_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_object* v_cs_343_; size_t v_j_344_; lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_cs_343_ = lean_ctor_get(v_x_340_, 0);
v_j_344_ = lean_usize_shift_right(v_x_341_, v_x_342_);
v___x_345_ = lean_usize_to_nat(v_j_344_);
v___x_346_ = lean_array_get_size(v_cs_343_);
v___x_347_ = lean_nat_dec_lt(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_dec(v___x_345_);
lean_dec(v_f_339_);
return v_x_340_;
}
else
{
lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_365_; 
lean_inc_ref(v_cs_343_);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_340_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v_x_340_, 0);
lean_dec(v_unused_366_);
v___x_349_ = v_x_340_;
v_isShared_350_ = v_isSharedCheck_365_;
goto v_resetjp_348_;
}
else
{
lean_dec(v_x_340_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_365_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; size_t v_i_354_; size_t v___x_355_; size_t v_shift_356_; lean_object* v_v_357_; lean_object* v___x_358_; lean_object* v_xs_x27_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_351_ = ((size_t)1ULL);
v___x_352_ = lean_usize_shift_left(v___x_351_, v_x_342_);
v___x_353_ = lean_usize_sub(v___x_352_, v___x_351_);
v_i_354_ = lean_usize_land(v_x_341_, v___x_353_);
v___x_355_ = ((size_t)5ULL);
v_shift_356_ = lean_usize_sub(v_x_342_, v___x_355_);
v_v_357_ = lean_array_fget(v_cs_343_, v___x_345_);
v___x_358_ = lean_box(0);
v_xs_x27_359_ = lean_array_fset(v_cs_343_, v___x_345_, v___x_358_);
v___x_360_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_339_, v_v_357_, v_i_354_, v_shift_356_);
v___x_361_ = lean_array_fset(v_xs_x27_359_, v___x_345_, v___x_360_);
lean_dec(v___x_345_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_361_);
v___x_363_ = v___x_349_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
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
else
{
lean_object* v_vs_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_vs_367_ = lean_ctor_get(v_x_340_, 0);
v___x_368_ = lean_usize_to_nat(v_x_341_);
v___x_369_ = lean_array_get_size(v_vs_367_);
v___x_370_ = lean_nat_dec_lt(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
lean_dec(v___x_368_);
lean_dec(v_f_339_);
return v_x_340_;
}
else
{
lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_382_; 
lean_inc_ref(v_vs_367_);
v_isSharedCheck_382_ = !lean_is_exclusive(v_x_340_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v_x_340_, 0);
lean_dec(v_unused_383_);
v___x_372_ = v_x_340_;
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
else
{
lean_dec(v_x_340_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_382_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_v_374_; lean_object* v___x_375_; lean_object* v_xs_x27_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v_v_374_ = lean_array_fget(v_vs_367_, v___x_368_);
v___x_375_ = lean_box(0);
v_xs_x27_376_ = lean_array_fset(v_vs_367_, v___x_368_, v___x_375_);
v___x_377_ = lean_apply_1(v_f_339_, v_v_374_);
v___x_378_ = lean_array_fset(v_xs_x27_376_, v___x_368_, v___x_377_);
lean_dec(v___x_368_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_378_);
v___x_380_ = v___x_372_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___redArg___boxed(lean_object* v_f_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
size_t v_x_96__boxed_388_; size_t v_x_97__boxed_389_; lean_object* v_res_390_; 
v_x_96__boxed_388_ = lean_unbox_usize(v_x_386_);
lean_dec(v_x_386_);
v_x_97__boxed_389_ = lean_unbox_usize(v_x_387_);
lean_dec(v_x_387_);
v_res_390_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_384_, v_x_385_, v_x_96__boxed_388_, v_x_97__boxed_389_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux(lean_object* v_00_u03b1_391_, lean_object* v_inst_392_, lean_object* v_f_393_, lean_object* v_x_394_, size_t v_x_395_, size_t v_x_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_393_, v_x_394_, v_x_395_, v_x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___boxed(lean_object* v_00_u03b1_398_, lean_object* v_inst_399_, lean_object* v_f_400_, lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_x_403_){
_start:
{
size_t v_x_174__boxed_404_; size_t v_x_175__boxed_405_; lean_object* v_res_406_; 
v_x_174__boxed_404_ = lean_unbox_usize(v_x_402_);
lean_dec(v_x_402_);
v_x_175__boxed_405_ = lean_unbox_usize(v_x_403_);
lean_dec(v_x_403_);
v_res_406_ = l_Lean_PersistentArray_modifyAux(v_00_u03b1_398_, v_inst_399_, v_f_400_, v_x_401_, v_x_174__boxed_404_, v_x_175__boxed_405_);
lean_dec(v_inst_399_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg(lean_object* v_t_407_, lean_object* v_i_408_, lean_object* v_f_409_){
_start:
{
lean_object* v_root_410_; lean_object* v_tail_411_; lean_object* v_size_412_; size_t v_shift_413_; lean_object* v_tailOff_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_438_; 
v_root_410_ = lean_ctor_get(v_t_407_, 0);
v_tail_411_ = lean_ctor_get(v_t_407_, 1);
v_size_412_ = lean_ctor_get(v_t_407_, 2);
v_shift_413_ = lean_ctor_get_usize(v_t_407_, 4);
v_tailOff_414_ = lean_ctor_get(v_t_407_, 3);
v_isSharedCheck_438_ = !lean_is_exclusive(v_t_407_);
if (v_isSharedCheck_438_ == 0)
{
v___x_416_ = v_t_407_;
v_isShared_417_ = v_isSharedCheck_438_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_tailOff_414_);
lean_inc(v_size_412_);
lean_inc(v_tail_411_);
lean_inc(v_root_410_);
lean_dec(v_t_407_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_438_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
uint8_t v___x_418_; 
v___x_418_ = lean_nat_dec_le(v_tailOff_414_, v_i_408_);
if (v___x_418_ == 0)
{
size_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_419_ = lean_usize_of_nat(v_i_408_);
v___x_420_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_409_, v_root_410_, v___x_419_, v_shift_413_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_420_);
v___x_422_ = v___x_416_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_tail_411_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_size_412_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_tailOff_414_);
lean_ctor_set_usize(v_reuseFailAlloc_423_, 4, v_shift_413_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v___x_424_ = lean_nat_sub(v_i_408_, v_tailOff_414_);
v___x_425_ = lean_array_get_size(v_tail_411_);
v___x_426_ = lean_nat_dec_lt(v___x_424_, v___x_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_428_; 
lean_dec(v___x_424_);
lean_dec(v_f_409_);
if (v_isShared_417_ == 0)
{
v___x_428_ = v___x_416_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_root_410_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_tail_411_);
lean_ctor_set(v_reuseFailAlloc_429_, 2, v_size_412_);
lean_ctor_set(v_reuseFailAlloc_429_, 3, v_tailOff_414_);
lean_ctor_set_usize(v_reuseFailAlloc_429_, 4, v_shift_413_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
else
{
lean_object* v_v_430_; lean_object* v___x_431_; lean_object* v_xs_x27_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v_v_430_ = lean_array_fget(v_tail_411_, v___x_424_);
v___x_431_ = lean_box(0);
v_xs_x27_432_ = lean_array_fset(v_tail_411_, v___x_424_, v___x_431_);
v___x_433_ = lean_apply_1(v_f_409_, v_v_430_);
v___x_434_ = lean_array_fset(v_xs_x27_432_, v___x_424_, v___x_433_);
lean_dec(v___x_424_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_434_);
v___x_436_ = v___x_416_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_root_410_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_size_412_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_tailOff_414_);
lean_ctor_set_usize(v_reuseFailAlloc_437_, 4, v_shift_413_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg___boxed(lean_object* v_t_439_, lean_object* v_i_440_, lean_object* v_f_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_PersistentArray_modify___redArg(v_t_439_, v_i_440_, v_f_441_);
lean_dec(v_i_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify(lean_object* v_00_u03b1_443_, lean_object* v_inst_444_, lean_object* v_t_445_, lean_object* v_i_446_, lean_object* v_f_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_PersistentArray_modify___redArg(v_t_445_, v_i_446_, v_f_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___boxed(lean_object* v_00_u03b1_449_, lean_object* v_inst_450_, lean_object* v_t_451_, lean_object* v_i_452_, lean_object* v_f_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_PersistentArray_modify(v_00_u03b1_449_, v_inst_450_, v_t_451_, v_i_452_, v_f_453_);
lean_dec(v_i_452_);
lean_dec(v_inst_450_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___redArg(size_t v_shift_455_, lean_object* v_a_456_){
_start:
{
size_t v___x_457_; uint8_t v___x_458_; 
v___x_457_ = ((size_t)0ULL);
v___x_458_ = lean_usize_dec_eq(v_shift_455_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; size_t v___x_460_; size_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_459_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
v___x_460_ = ((size_t)5ULL);
v___x_461_ = lean_usize_sub(v_shift_455_, v___x_460_);
v___x_462_ = l_Lean_PersistentArray_mkNewPath___redArg(v___x_461_, v_a_456_);
v___x_463_ = lean_array_push(v___x_459_, v___x_462_);
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
return v___x_464_;
}
else
{
lean_object* v___x_465_; 
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v_a_456_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___redArg___boxed(lean_object* v_shift_466_, lean_object* v_a_467_){
_start:
{
size_t v_shift_boxed_468_; lean_object* v_res_469_; 
v_shift_boxed_468_ = lean_unbox_usize(v_shift_466_);
lean_dec(v_shift_466_);
v_res_469_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_boxed_468_, v_a_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath(lean_object* v_00_u03b1_470_, size_t v_shift_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_471_, v_a_472_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___boxed(lean_object* v_00_u03b1_474_, lean_object* v_shift_475_, lean_object* v_a_476_){
_start:
{
size_t v_shift_boxed_477_; lean_object* v_res_478_; 
v_shift_boxed_477_ = lean_unbox_usize(v_shift_475_);
lean_dec(v_shift_475_);
v_res_478_ = l_Lean_PersistentArray_mkNewPath(v_00_u03b1_474_, v_shift_boxed_477_, v_a_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg(lean_object* v_x_479_, size_t v_x_480_, size_t v_x_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
lean_object* v_cs_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_517_; 
v_cs_483_ = lean_ctor_get(v_x_479_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v_x_479_);
if (v_isSharedCheck_517_ == 0)
{
v___x_485_ = v_x_479_;
v_isShared_486_ = v_isSharedCheck_517_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_cs_483_);
lean_dec(v_x_479_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_517_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
size_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = ((size_t)32ULL);
v___x_488_ = lean_usize_dec_lt(v_x_480_, v___x_487_);
if (v___x_488_ == 0)
{
size_t v_j_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v_shift_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_j_489_ = lean_usize_shift_right(v_x_480_, v_x_481_);
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_shift_left(v___x_490_, v_x_481_);
v___x_492_ = ((size_t)5ULL);
v_shift_493_ = lean_usize_sub(v_x_481_, v___x_492_);
v___x_494_ = lean_usize_to_nat(v_j_489_);
v___x_495_ = lean_array_get_size(v_cs_483_);
v___x_496_ = lean_nat_dec_lt(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
lean_dec(v___x_494_);
v___x_497_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_493_, v_x_482_);
v___x_498_ = lean_array_push(v_cs_483_, v___x_497_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_498_);
v___x_500_ = v___x_485_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
else
{
size_t v___x_502_; size_t v_i_503_; lean_object* v_v_504_; lean_object* v___x_505_; lean_object* v_xs_x27_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_502_ = lean_usize_sub(v___x_491_, v___x_490_);
v_i_503_ = lean_usize_land(v_x_480_, v___x_502_);
v_v_504_ = lean_array_fget(v_cs_483_, v___x_494_);
v___x_505_ = lean_box(0);
v_xs_x27_506_ = lean_array_fset(v_cs_483_, v___x_494_, v___x_505_);
v___x_507_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_v_504_, v_i_503_, v_shift_493_, v_x_482_);
v___x_508_ = lean_array_fset(v_xs_x27_506_, v___x_494_, v___x_507_);
lean_dec(v___x_494_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_508_);
v___x_510_ = v___x_485_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v___x_513_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set_tag(v___x_485_, 1);
lean_ctor_set(v___x_485_, 0, v_x_482_);
v___x_513_ = v___x_485_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_x_482_);
v___x_513_ = v_reuseFailAlloc_516_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_array_push(v_cs_483_, v___x_513_);
v___x_515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
return v___x_515_;
}
}
}
}
else
{
lean_dec_ref(v_x_482_);
return v_x_479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg___boxed(lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
size_t v_x_102__boxed_522_; size_t v_x_103__boxed_523_; lean_object* v_res_524_; 
v_x_102__boxed_522_ = lean_unbox_usize(v_x_519_);
lean_dec(v_x_519_);
v_x_103__boxed_523_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_res_524_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_518_, v_x_102__boxed_522_, v_x_103__boxed_523_, v_x_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf(lean_object* v_00_u03b1_525_, lean_object* v_x_526_, size_t v_x_527_, size_t v_x_528_, lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_526_, v_x_527_, v_x_528_, v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___boxed(lean_object* v_00_u03b1_531_, lean_object* v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
size_t v_x_174__boxed_536_; size_t v_x_175__boxed_537_; lean_object* v_res_538_; 
v_x_174__boxed_536_ = lean_unbox_usize(v_x_533_);
lean_dec(v_x_533_);
v_x_175__boxed_537_ = lean_unbox_usize(v_x_534_);
lean_dec(v_x_534_);
v_res_538_ = l_Lean_PersistentArray_insertNewLeaf(v_00_u03b1_531_, v_x_532_, v_x_174__boxed_536_, v_x_175__boxed_537_, v_x_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail___redArg(lean_object* v_t_541_){
_start:
{
lean_object* v_root_542_; lean_object* v_tail_543_; lean_object* v_size_544_; size_t v_shift_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_572_; 
v_root_542_ = lean_ctor_get(v_t_541_, 0);
v_tail_543_ = lean_ctor_get(v_t_541_, 1);
v_size_544_ = lean_ctor_get(v_t_541_, 2);
v_shift_545_ = lean_ctor_get_usize(v_t_541_, 4);
v_isSharedCheck_572_ = !lean_is_exclusive(v_t_541_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; 
v_unused_573_ = lean_ctor_get(v_t_541_, 3);
lean_dec(v_unused_573_);
v___x_547_ = v_t_541_;
v_isShared_548_ = v_isSharedCheck_572_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_size_544_);
lean_inc(v_tail_543_);
lean_inc(v_root_542_);
lean_dec(v_t_541_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_572_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
size_t v___x_549_; size_t v___x_550_; size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_549_ = ((size_t)1ULL);
v___x_550_ = ((size_t)5ULL);
v___x_551_ = lean_usize_add(v_shift_545_, v___x_550_);
v___x_552_ = lean_usize_shift_left(v___x_549_, v___x_551_);
v___x_553_ = lean_usize_to_nat(v___x_552_);
v___x_554_ = lean_nat_dec_le(v_size_544_, v___x_553_);
lean_dec(v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v_n_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_555_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
v_n_556_ = lean_array_push(v___x_555_, v_root_542_);
v___x_557_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_545_, v_tail_543_);
v___x_558_ = lean_array_push(v_n_556_, v___x_557_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
v___x_560_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
lean_inc(v_size_544_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 3, v_size_544_);
lean_ctor_set(v___x_547_, 1, v___x_560_);
lean_ctor_set(v___x_547_, 0, v___x_559_);
v___x_562_ = v___x_547_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_563_, 1, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_563_, 2, v_size_544_);
lean_ctor_set(v_reuseFailAlloc_563_, 3, v_size_544_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_ctor_set_usize(v___x_562_, 4, v___x_551_);
return v___x_562_;
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; size_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_570_; 
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = lean_nat_sub(v_size_544_, v___x_564_);
v___x_566_ = lean_usize_of_nat(v___x_565_);
lean_dec(v___x_565_);
v___x_567_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_root_542_, v___x_566_, v_shift_545_, v_tail_543_);
v___x_568_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
lean_inc(v_size_544_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 3, v_size_544_);
lean_ctor_set(v___x_547_, 1, v___x_568_);
lean_ctor_set(v___x_547_, 0, v___x_567_);
v___x_570_ = v___x_547_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_size_544_);
lean_ctor_set(v_reuseFailAlloc_571_, 3, v_size_544_);
lean_ctor_set_usize(v_reuseFailAlloc_571_, 4, v_shift_545_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail(lean_object* v_00_u03b1_574_, lean_object* v_t_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_PersistentArray_mkNewTail___redArg(v_t_575_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__0(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = l_System_Platform_numBits;
v___x_578_ = lean_unsigned_to_nat(2u);
v___x_579_ = lean_nat_pow(v___x_578_, v___x_577_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__1(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = lean_unsigned_to_nat(3u);
v___x_581_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__0, &l_Lean_PersistentArray_tooBig___closed__0_once, _init_l_Lean_PersistentArray_tooBig___closed__0);
v___x_582_ = lean_nat_shiftr(v___x_581_, v___x_580_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig(void){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__1, &l_Lean_PersistentArray_tooBig___closed__1_once, _init_l_Lean_PersistentArray_tooBig___closed__1);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push___redArg(lean_object* v_t_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_root_586_; lean_object* v_tail_587_; lean_object* v_size_588_; size_t v_shift_589_; lean_object* v_tailOff_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_606_; 
v_root_586_ = lean_ctor_get(v_t_584_, 0);
v_tail_587_ = lean_ctor_get(v_t_584_, 1);
v_size_588_ = lean_ctor_get(v_t_584_, 2);
v_shift_589_ = lean_ctor_get_usize(v_t_584_, 4);
v_tailOff_590_ = lean_ctor_get(v_t_584_, 3);
v_isSharedCheck_606_ = !lean_is_exclusive(v_t_584_);
if (v_isSharedCheck_606_ == 0)
{
v___x_592_ = v_t_584_;
v_isShared_593_ = v_isSharedCheck_606_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_tailOff_590_);
lean_inc(v_size_588_);
lean_inc(v_tail_587_);
lean_inc(v_root_586_);
lean_dec(v_t_584_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_606_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v_r_598_; 
v___x_594_ = lean_array_push(v_tail_587_, v_a_585_);
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_nat_add(v_size_588_, v___x_595_);
lean_inc_ref(v___x_594_);
if (v_isShared_593_ == 0)
{
lean_ctor_set(v___x_592_, 2, v___x_596_);
lean_ctor_set(v___x_592_, 1, v___x_594_);
v_r_598_ = v___x_592_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_root_586_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_tailOff_590_);
lean_ctor_set_usize(v_reuseFailAlloc_605_, 4, v_shift_589_);
v_r_598_ = v_reuseFailAlloc_605_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_599_ = lean_array_get_size(v___x_594_);
lean_dec_ref(v___x_594_);
v___x_600_ = lean_unsigned_to_nat(32u);
v___x_601_ = lean_nat_dec_lt(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_602_ = l_Lean_PersistentArray_tooBig;
v___x_603_ = lean_nat_dec_le(v___x_602_, v_size_588_);
lean_dec(v_size_588_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_PersistentArray_mkNewTail___redArg(v_r_598_);
return v___x_604_;
}
else
{
return v_r_598_;
}
}
else
{
lean_dec(v_size_588_);
return v_r_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push(lean_object* v_00_u03b1_607_, lean_object* v_t_608_, lean_object* v_a_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_PersistentArray_push___redArg(v_t_608_, v_a_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_rightpad_go___redArg(lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_zero_614_; uint8_t v_isZero_615_; 
v_zero_614_ = lean_unsigned_to_nat(0u);
v_isZero_615_ = lean_nat_dec_eq(v_a_612_, v_zero_614_);
if (v_isZero_615_ == 1)
{
lean_dec(v_a_612_);
lean_dec(v_a_611_);
return v_a_613_;
}
else
{
lean_object* v_one_616_; lean_object* v_n_617_; lean_object* v___x_618_; 
v_one_616_ = lean_unsigned_to_nat(1u);
v_n_617_ = lean_nat_sub(v_a_612_, v_one_616_);
lean_dec(v_a_612_);
lean_inc(v_a_611_);
v___x_618_ = l_Lean_PersistentArray_push___redArg(v_a_613_, v_a_611_);
v_a_612_ = v_n_617_;
v_a_613_ = v___x_618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_rightpad_go(lean_object* v_00_u03b1_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_rightpad_go___redArg(v_a_621_, v_a_622_, v_a_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_rightpad___redArg(lean_object* v_n_625_, lean_object* v_a_626_, lean_object* v_t_627_){
_start:
{
lean_object* v_size_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v_size_628_ = lean_ctor_get(v_t_627_, 2);
v___x_629_ = lean_nat_sub(v_n_625_, v_size_628_);
v___x_630_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_rightpad_go___redArg(v_a_626_, v___x_629_, v_t_627_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_rightpad___redArg___boxed(lean_object* v_n_631_, lean_object* v_a_632_, lean_object* v_t_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_PersistentArray_rightpad___redArg(v_n_631_, v_a_632_, v_t_633_);
lean_dec(v_n_631_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_rightpad(lean_object* v_00_u03b1_635_, lean_object* v_n_636_, lean_object* v_a_637_, lean_object* v_t_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_PersistentArray_rightpad___redArg(v_n_636_, v_a_637_, v_t_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_rightpad___boxed(lean_object* v_00_u03b1_640_, lean_object* v_n_641_, lean_object* v_a_642_, lean_object* v_t_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_PersistentArray_rightpad(v_00_u03b1_640_, v_n_641_, v_a_642_, v_t_643_);
lean_dec(v_n_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg(){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(32u);
v___x_647_ = lean_mk_empty_array_with_capacity(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg___boxed(lean_object* v___dummy_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
return v_res_649_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0(void){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_object* v_00_u03b1_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_653_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf___redArg(lean_object* v_x_656_){
_start:
{
if (lean_obj_tag(v_x_656_) == 0)
{
lean_object* v_cs_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_707_; 
v_cs_657_ = lean_ctor_get(v_x_656_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_656_);
if (v_isSharedCheck_707_ == 0)
{
v___x_659_ = v_x_656_;
v_isShared_660_ = v_isSharedCheck_707_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_cs_657_);
lean_dec(v_x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_707_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_661_ = lean_array_get_size(v_cs_657_);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_nat_dec_eq(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v_idx_665_; lean_object* v_last_666_; lean_object* v___x_667_; lean_object* v_fst_668_; 
v___x_664_ = lean_unsigned_to_nat(1u);
v_idx_665_ = lean_nat_sub(v___x_661_, v___x_664_);
v_last_666_ = lean_array_fget_borrowed(v_cs_657_, v_idx_665_);
lean_inc(v_last_666_);
v___x_667_ = l_Lean_PersistentArray_popLeaf___redArg(v_last_666_);
v_fst_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_fst_668_);
if (lean_obj_tag(v_fst_668_) == 0)
{
lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_676_; 
lean_dec(v_idx_665_);
lean_del_object(v___x_659_);
lean_dec_ref(v_cs_657_);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_676_ == 0)
{
lean_object* v_unused_677_; lean_object* v_unused_678_; 
v_unused_677_ = lean_ctor_get(v___x_667_, 1);
lean_dec(v_unused_677_);
v_unused_678_ = lean_ctor_get(v___x_667_, 0);
lean_dec(v_unused_678_);
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
else
{
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_676_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v___x_672_);
v___x_674_ = v___x_670_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_fst_668_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
lean_object* v_snd_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_704_; 
v_snd_679_ = lean_ctor_get(v___x_667_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v___x_667_, 0);
lean_dec(v_unused_705_);
v___x_681_ = v___x_667_;
v_isShared_682_ = v_isSharedCheck_704_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_snd_679_);
lean_dec(v___x_667_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_704_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v_cs_x27_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_683_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v_cs_x27_684_ = lean_array_fset(v_cs_657_, v_idx_665_, v___x_683_);
v___x_685_ = lean_array_get_size(v_snd_679_);
v___x_686_ = lean_nat_dec_eq(v___x_685_, v___x_662_);
if (v___x_686_ == 0)
{
lean_object* v___x_688_; 
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_snd_679_);
v___x_688_ = v___x_659_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_snd_679_);
v___x_688_ = v_reuseFailAlloc_693_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_array_fset(v_cs_x27_684_, v_idx_665_, v___x_688_);
lean_dec(v_idx_665_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_689_);
v___x_691_ = v___x_681_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fst_668_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_object* v_cs_x27_694_; lean_object* v___x_695_; uint8_t v___x_696_; 
lean_dec(v_snd_679_);
lean_dec(v_idx_665_);
lean_del_object(v___x_659_);
v_cs_x27_694_ = lean_array_pop(v_cs_x27_684_);
v___x_695_ = lean_array_get_size(v_cs_x27_694_);
v___x_696_ = lean_nat_dec_eq(v___x_695_, v___x_662_);
if (v___x_696_ == 0)
{
lean_object* v___x_698_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v_cs_x27_694_);
v___x_698_ = v___x_681_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_fst_668_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_cs_x27_694_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
else
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec_ref(v_cs_x27_694_);
v___x_700_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_700_);
v___x_702_ = v___x_681_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_fst_668_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
}
else
{
lean_object* v___x_706_; 
lean_del_object(v___x_659_);
lean_dec_ref(v_cs_657_);
v___x_706_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
return v___x_706_;
}
}
}
else
{
lean_object* v_vs_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v_vs_708_ = lean_ctor_get(v_x_656_, 0);
lean_inc_ref(v_vs_708_);
lean_dec_ref_known(v_x_656_, 1);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v_vs_708_);
v___x_710_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
v___x_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
return v___x_711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf(lean_object* v_00_u03b1_712_, lean_object* v_x_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_PersistentArray_popLeaf___redArg(v_x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop___redArg(lean_object* v_t_715_){
_start:
{
lean_object* v_root_716_; lean_object* v_tail_717_; lean_object* v_size_718_; size_t v_shift_719_; lean_object* v_tailOff_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_root_716_ = lean_ctor_get(v_t_715_, 0);
v_tail_717_ = lean_ctor_get(v_t_715_, 1);
v_size_718_ = lean_ctor_get(v_t_715_, 2);
v_shift_719_ = lean_ctor_get_usize(v_t_715_, 4);
v_tailOff_720_ = lean_ctor_get(v_t_715_, 3);
v___x_721_ = lean_unsigned_to_nat(0u);
v___x_722_ = lean_array_get_size(v_tail_717_);
v___x_723_ = lean_nat_dec_lt(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; lean_object* v_fst_725_; 
lean_inc_ref(v_root_716_);
v___x_724_ = l_Lean_PersistentArray_popLeaf___redArg(v_root_716_);
v_fst_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_fst_725_);
if (lean_obj_tag(v_fst_725_) == 0)
{
lean_dec_ref(v___x_724_);
return v_t_715_;
}
else
{
lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_754_; 
lean_inc(v_size_718_);
v_isSharedCheck_754_ = !lean_is_exclusive(v_t_715_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; lean_object* v_unused_756_; lean_object* v_unused_757_; lean_object* v_unused_758_; 
v_unused_755_ = lean_ctor_get(v_t_715_, 3);
lean_dec(v_unused_755_);
v_unused_756_ = lean_ctor_get(v_t_715_, 2);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_t_715_, 1);
lean_dec(v_unused_757_);
v_unused_758_ = lean_ctor_get(v_t_715_, 0);
lean_dec(v_unused_758_);
v___x_727_ = v_t_715_;
v_isShared_728_ = v_isSharedCheck_754_;
goto v_resetjp_726_;
}
else
{
lean_dec(v_t_715_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_754_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_snd_729_; lean_object* v_val_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_753_; 
v_snd_729_ = lean_ctor_get(v___x_724_, 1);
lean_inc(v_snd_729_);
lean_dec_ref(v___x_724_);
v_val_730_ = lean_ctor_get(v_fst_725_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v_fst_725_);
if (v_isSharedCheck_753_ == 0)
{
v___x_732_ = v_fst_725_;
v_isShared_733_ = v_isSharedCheck_753_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_val_730_);
lean_dec(v_fst_725_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_753_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v_last_734_; lean_object* v___x_735_; lean_object* v_newSize_736_; lean_object* v___x_737_; lean_object* v_newTailOff_738_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_last_734_ = lean_array_pop(v_val_730_);
v___x_735_ = lean_unsigned_to_nat(1u);
v_newSize_736_ = lean_nat_sub(v_size_718_, v___x_735_);
lean_dec(v_size_718_);
v___x_737_ = lean_array_get_size(v_last_734_);
v_newTailOff_738_ = lean_nat_sub(v_newSize_736_, v___x_737_);
v___x_746_ = lean_array_get_size(v_snd_729_);
v___x_747_ = lean_nat_dec_eq(v___x_746_, v___x_735_);
if (v___x_747_ == 0)
{
goto v___jp_739_;
}
else
{
lean_object* v___x_748_; uint8_t v___x_749_; 
v___x_748_ = lean_array_fget_borrowed(v_snd_729_, v___x_721_);
v___x_749_ = l_Lean_PersistentArrayNode_isNode___redArg(v___x_748_);
if (v___x_749_ == 0)
{
goto v___jp_739_;
}
else
{
size_t v___x_750_; size_t v___x_751_; lean_object* v___x_752_; 
lean_inc(v___x_748_);
lean_del_object(v___x_732_);
lean_dec(v_snd_729_);
lean_del_object(v___x_727_);
v___x_750_ = ((size_t)5ULL);
v___x_751_ = lean_usize_sub(v_shift_719_, v___x_750_);
v___x_752_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_752_, 0, v___x_748_);
lean_ctor_set(v___x_752_, 1, v_last_734_);
lean_ctor_set(v___x_752_, 2, v_newSize_736_);
lean_ctor_set(v___x_752_, 3, v_newTailOff_738_);
lean_ctor_set_usize(v___x_752_, 4, v___x_751_);
return v___x_752_;
}
}
v___jp_739_:
{
lean_object* v___x_741_; 
if (v_isShared_733_ == 0)
{
lean_ctor_set_tag(v___x_732_, 0);
lean_ctor_set(v___x_732_, 0, v_snd_729_);
v___x_741_ = v___x_732_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_snd_729_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 3, v_newTailOff_738_);
lean_ctor_set(v___x_727_, 2, v_newSize_736_);
lean_ctor_set(v___x_727_, 1, v_last_734_);
lean_ctor_set(v___x_727_, 0, v___x_741_);
v___x_743_ = v___x_727_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_last_734_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_newSize_736_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v_newTailOff_738_);
lean_ctor_set_usize(v_reuseFailAlloc_744_, 4, v_shift_719_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_768_; 
lean_inc(v_tailOff_720_);
lean_inc(v_size_718_);
lean_inc_ref(v_tail_717_);
lean_inc_ref(v_root_716_);
v_isSharedCheck_768_ = !lean_is_exclusive(v_t_715_);
if (v_isSharedCheck_768_ == 0)
{
lean_object* v_unused_769_; lean_object* v_unused_770_; lean_object* v_unused_771_; lean_object* v_unused_772_; 
v_unused_769_ = lean_ctor_get(v_t_715_, 3);
lean_dec(v_unused_769_);
v_unused_770_ = lean_ctor_get(v_t_715_, 2);
lean_dec(v_unused_770_);
v_unused_771_ = lean_ctor_get(v_t_715_, 1);
lean_dec(v_unused_771_);
v_unused_772_ = lean_ctor_get(v_t_715_, 0);
lean_dec(v_unused_772_);
v___x_760_ = v_t_715_;
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
else
{
lean_dec(v_t_715_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_768_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_766_; 
v___x_762_ = lean_array_pop(v_tail_717_);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_sub(v_size_718_, v___x_763_);
lean_dec(v_size_718_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 2, v___x_764_);
lean_ctor_set(v___x_760_, 1, v___x_762_);
v___x_766_ = v___x_760_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_root_716_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v___x_762_);
lean_ctor_set(v_reuseFailAlloc_767_, 2, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_767_, 3, v_tailOff_720_);
lean_ctor_set_usize(v_reuseFailAlloc_767_, 4, v_shift_719_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop(lean_object* v_00_u03b1_773_, lean_object* v_t_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_PersistentArray_pop___redArg(v_t_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(lean_object* v_inst_776_, lean_object* v_f_777_, lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
if (lean_obj_tag(v_x_778_) == 0)
{
lean_object* v_toApplicative_780_; lean_object* v_cs_781_; lean_object* v_toPure_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v_toApplicative_780_ = lean_ctor_get(v_inst_776_, 0);
v_cs_781_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_cs_781_);
lean_dec_ref_known(v_x_778_, 1);
v_toPure_782_ = lean_ctor_get(v_toApplicative_780_, 1);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_array_get_size(v_cs_781_);
v___x_785_ = lean_nat_dec_lt(v___x_783_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
lean_inc(v_toPure_782_);
lean_dec_ref(v_cs_781_);
lean_dec(v_f_777_);
lean_dec_ref(v_inst_776_);
v___x_786_ = lean_apply_2(v_toPure_782_, lean_box(0), v_x_779_);
return v___x_786_;
}
else
{
lean_object* v___f_787_; size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
lean_inc_ref(v_inst_776_);
v___f_787_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_787_, 0, v_inst_776_);
lean_closure_set(v___f_787_, 1, v_f_777_);
v___x_788_ = ((size_t)0ULL);
v___x_789_ = lean_usize_of_nat(v___x_784_);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_776_, v___f_787_, v_cs_781_, v___x_788_, v___x_789_, v_x_779_);
return v___x_790_;
}
}
else
{
lean_object* v_toApplicative_791_; lean_object* v_vs_792_; lean_object* v_toPure_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_toApplicative_791_ = lean_ctor_get(v_inst_776_, 0);
v_vs_792_ = lean_ctor_get(v_x_778_, 0);
lean_inc_ref(v_vs_792_);
lean_dec_ref_known(v_x_778_, 1);
v_toPure_793_ = lean_ctor_get(v_toApplicative_791_, 1);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_array_get_size(v_vs_792_);
v___x_796_ = lean_nat_dec_lt(v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; 
lean_inc(v_toPure_793_);
lean_dec_ref(v_vs_792_);
lean_dec(v_f_777_);
lean_dec_ref(v_inst_776_);
v___x_797_ = lean_apply_2(v_toPure_793_, lean_box(0), v_x_779_);
return v___x_797_;
}
else
{
size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
v___x_798_ = ((size_t)0ULL);
v___x_799_ = lean_usize_of_nat(v___x_795_);
v___x_800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_776_, v_f_777_, v_vs_792_, v___x_798_, v___x_799_, v_x_779_);
return v___x_800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0(lean_object* v_inst_801_, lean_object* v_f_802_, lean_object* v_b_803_, lean_object* v_c_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_801_, v_f_802_, v_c_804_, v_b_803_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux(lean_object* v_00_u03b1_806_, lean_object* v_m_807_, lean_object* v_inst_808_, lean_object* v_00_u03b2_809_, lean_object* v_f_810_, lean_object* v_x_811_, lean_object* v_x_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_808_, v_f_810_, v_x_811_, v_x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(lean_object* v_toApplicative_814_, lean_object* v_j_815_, lean_object* v_cs_816_, lean_object* v_inst_817_, lean_object* v___f_818_, lean_object* v_b_819_){
_start:
{
lean_object* v_toPure_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; 
v_toPure_820_ = lean_ctor_get(v_toApplicative_814_, 1);
lean_inc(v_toPure_820_);
lean_dec_ref(v_toApplicative_814_);
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_add(v_j_815_, v___x_821_);
v___x_823_ = lean_array_get_size(v_cs_816_);
v___x_824_ = lean_nat_dec_lt(v___x_822_, v___x_823_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; 
lean_dec(v___x_822_);
lean_dec(v___f_818_);
lean_dec_ref(v_inst_817_);
lean_dec_ref(v_cs_816_);
v___x_825_ = lean_apply_2(v_toPure_820_, lean_box(0), v_b_819_);
return v___x_825_;
}
else
{
size_t v___x_826_; size_t v___x_827_; lean_object* v___x_828_; 
lean_dec(v_toPure_820_);
v___x_826_ = lean_usize_of_nat(v___x_822_);
lean_dec(v___x_822_);
v___x_827_ = lean_usize_of_nat(v___x_823_);
v___x_828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_817_, v___f_818_, v_cs_816_, v___x_826_, v___x_827_, v_b_819_);
return v___x_828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_829_, lean_object* v_j_830_, lean_object* v_cs_831_, lean_object* v_inst_832_, lean_object* v___f_833_, lean_object* v_b_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(v_toApplicative_829_, v_j_830_, v_cs_831_, v_inst_832_, v___f_833_, v_b_834_);
lean_dec(v_j_830_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(lean_object* v_inst_836_, lean_object* v_f_837_, lean_object* v_x_838_, size_t v_x_839_, size_t v_x_840_, lean_object* v_x_841_){
_start:
{
if (lean_obj_tag(v_x_838_) == 0)
{
lean_object* v_toApplicative_842_; lean_object* v_toBind_843_; lean_object* v_cs_844_; lean_object* v___f_845_; lean_object* v___x_846_; size_t v___x_847_; lean_object* v_j_848_; lean_object* v___f_849_; lean_object* v___x_850_; size_t v___x_851_; size_t v___x_852_; size_t v___x_853_; size_t v___x_854_; size_t v___x_855_; size_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_toApplicative_842_ = lean_ctor_get(v_inst_836_, 0);
v_toBind_843_ = lean_ctor_get(v_inst_836_, 1);
lean_inc(v_toBind_843_);
v_cs_844_ = lean_ctor_get(v_x_838_, 0);
lean_inc_ref_n(v_cs_844_, 2);
lean_dec_ref_known(v_x_838_, 1);
lean_inc(v_f_837_);
lean_inc_ref_n(v_inst_836_, 2);
v___f_845_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_845_, 0, v_inst_836_);
lean_closure_set(v___f_845_, 1, v_f_837_);
v___x_846_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_847_ = lean_usize_shift_right(v_x_839_, v_x_840_);
v_j_848_ = lean_usize_to_nat(v___x_847_);
lean_inc(v_j_848_);
lean_inc_ref(v_toApplicative_842_);
v___f_849_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_849_, 0, v_toApplicative_842_);
lean_closure_set(v___f_849_, 1, v_j_848_);
lean_closure_set(v___f_849_, 2, v_cs_844_);
lean_closure_set(v___f_849_, 3, v_inst_836_);
lean_closure_set(v___f_849_, 4, v___f_845_);
v___x_850_ = lean_array_get(v___x_846_, v_cs_844_, v_j_848_);
lean_dec(v_j_848_);
lean_dec_ref(v_cs_844_);
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_shift_left(v___x_851_, v_x_840_);
v___x_853_ = lean_usize_sub(v___x_852_, v___x_851_);
v___x_854_ = lean_usize_land(v_x_839_, v___x_853_);
v___x_855_ = ((size_t)5ULL);
v___x_856_ = lean_usize_sub(v_x_840_, v___x_855_);
v___x_857_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_836_, v_f_837_, v___x_850_, v___x_854_, v___x_856_, v_x_841_);
v___x_858_ = lean_apply_4(v_toBind_843_, lean_box(0), lean_box(0), v___x_857_, v___f_849_);
return v___x_858_;
}
else
{
lean_object* v_toApplicative_859_; lean_object* v_vs_860_; lean_object* v_toPure_861_; lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v_toApplicative_859_ = lean_ctor_get(v_inst_836_, 0);
v_vs_860_ = lean_ctor_get(v_x_838_, 0);
lean_inc_ref(v_vs_860_);
lean_dec_ref_known(v_x_838_, 1);
v_toPure_861_ = lean_ctor_get(v_toApplicative_859_, 1);
v___x_862_ = lean_usize_to_nat(v_x_839_);
v___x_863_ = lean_array_get_size(v_vs_860_);
v___x_864_ = lean_nat_dec_lt(v___x_862_, v___x_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
lean_inc(v_toPure_861_);
lean_dec(v___x_862_);
lean_dec_ref(v_vs_860_);
lean_dec(v_f_837_);
lean_dec_ref(v_inst_836_);
v___x_865_ = lean_apply_2(v_toPure_861_, lean_box(0), v_x_841_);
return v___x_865_;
}
else
{
size_t v___x_866_; size_t v___x_867_; lean_object* v___x_868_; 
v___x_866_ = lean_usize_of_nat(v___x_862_);
lean_dec(v___x_862_);
v___x_867_ = lean_usize_of_nat(v___x_863_);
v___x_868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_836_, v_f_837_, v_vs_860_, v___x_866_, v___x_867_, v_x_841_);
return v___x_868_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___boxed(lean_object* v_inst_869_, lean_object* v_f_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_){
_start:
{
size_t v_x_192__boxed_875_; size_t v_x_193__boxed_876_; lean_object* v_res_877_; 
v_x_192__boxed_875_ = lean_unbox_usize(v_x_872_);
lean_dec(v_x_872_);
v_x_193__boxed_876_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_res_877_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_869_, v_f_870_, v_x_871_, v_x_192__boxed_875_, v_x_193__boxed_876_, v_x_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(lean_object* v_00_u03b1_878_, lean_object* v_m_879_, lean_object* v_inst_880_, lean_object* v_00_u03b2_881_, lean_object* v_f_882_, lean_object* v_x_883_, size_t v_x_884_, size_t v_x_885_, lean_object* v_x_886_){
_start:
{
lean_object* v___x_887_; 
v___x_887_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_880_, v_f_882_, v_x_883_, v_x_884_, v_x_885_, v_x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___boxed(lean_object* v_00_u03b1_888_, lean_object* v_m_889_, lean_object* v_inst_890_, lean_object* v_00_u03b2_891_, lean_object* v_f_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_x_896_){
_start:
{
size_t v_x_251__boxed_897_; size_t v_x_252__boxed_898_; lean_object* v_res_899_; 
v_x_251__boxed_897_ = lean_unbox_usize(v_x_894_);
lean_dec(v_x_894_);
v_x_252__boxed_898_ = lean_unbox_usize(v_x_895_);
lean_dec(v_x_895_);
v_res_899_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(v_00_u03b1_888_, v_m_889_, v_inst_890_, v_00_u03b2_891_, v_f_892_, v_x_893_, v_x_251__boxed_897_, v_x_252__boxed_898_, v_x_896_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0(lean_object* v_toApplicative_900_, lean_object* v_tail_901_, lean_object* v___x_902_, lean_object* v_inst_903_, lean_object* v_f_904_, lean_object* v_b_905_){
_start:
{
lean_object* v_toPure_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_toPure_906_ = lean_ctor_get(v_toApplicative_900_, 1);
lean_inc(v_toPure_906_);
lean_dec_ref(v_toApplicative_900_);
v___x_907_ = lean_array_get_size(v_tail_901_);
v___x_908_ = lean_nat_dec_lt(v___x_902_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
lean_dec(v_f_904_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_tail_901_);
v___x_909_ = lean_apply_2(v_toPure_906_, lean_box(0), v_b_905_);
return v___x_909_;
}
else
{
size_t v___x_910_; size_t v___x_911_; lean_object* v___x_912_; 
lean_dec(v_toPure_906_);
v___x_910_ = ((size_t)0ULL);
v___x_911_ = lean_usize_of_nat(v___x_907_);
v___x_912_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_903_, v_f_904_, v_tail_901_, v___x_910_, v___x_911_, v_b_905_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed(lean_object* v_toApplicative_913_, lean_object* v_tail_914_, lean_object* v___x_915_, lean_object* v_inst_916_, lean_object* v_f_917_, lean_object* v_b_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lean_PersistentArray_foldlM___redArg___lam__0(v_toApplicative_913_, v_tail_914_, v___x_915_, v_inst_916_, v_f_917_, v_b_918_);
lean_dec(v___x_915_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object* v_inst_920_, lean_object* v_t_921_, lean_object* v_f_922_, lean_object* v_init_923_, lean_object* v_start_924_){
_start:
{
lean_object* v_toApplicative_925_; lean_object* v_toBind_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_toApplicative_925_ = lean_ctor_get(v_inst_920_, 0);
v_toBind_926_ = lean_ctor_get(v_inst_920_, 1);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_nat_dec_eq(v_start_924_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v_root_929_; lean_object* v_tail_930_; size_t v_shift_931_; lean_object* v_tailOff_932_; uint8_t v___x_933_; 
v_root_929_ = lean_ctor_get(v_t_921_, 0);
lean_inc_ref(v_root_929_);
v_tail_930_ = lean_ctor_get(v_t_921_, 1);
lean_inc_ref(v_tail_930_);
v_shift_931_ = lean_ctor_get_usize(v_t_921_, 4);
v_tailOff_932_ = lean_ctor_get(v_t_921_, 3);
lean_inc(v_tailOff_932_);
lean_dec_ref(v_t_921_);
v___x_933_ = lean_nat_dec_le(v_tailOff_932_, v_start_924_);
if (v___x_933_ == 0)
{
lean_object* v___f_934_; size_t v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_inc(v_toBind_926_);
lean_dec(v_tailOff_932_);
lean_inc(v_f_922_);
lean_inc_ref(v_inst_920_);
lean_inc_ref(v_toApplicative_925_);
v___f_934_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_934_, 0, v_toApplicative_925_);
lean_closure_set(v___f_934_, 1, v_tail_930_);
lean_closure_set(v___f_934_, 2, v___x_927_);
lean_closure_set(v___f_934_, 3, v_inst_920_);
lean_closure_set(v___f_934_, 4, v_f_922_);
v___x_935_ = lean_usize_of_nat(v_start_924_);
v___x_936_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_920_, v_f_922_, v_root_929_, v___x_935_, v_shift_931_, v_init_923_);
v___x_937_ = lean_apply_4(v_toBind_926_, lean_box(0), lean_box(0), v___x_936_, v___f_934_);
return v___x_937_;
}
else
{
lean_object* v_toPure_938_; lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
lean_dec_ref(v_root_929_);
v_toPure_938_ = lean_ctor_get(v_toApplicative_925_, 1);
v___x_939_ = lean_nat_sub(v_start_924_, v_tailOff_932_);
lean_dec(v_tailOff_932_);
v___x_940_ = lean_array_get_size(v_tail_930_);
v___x_941_ = lean_nat_dec_lt(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_inc(v_toPure_938_);
lean_dec(v___x_939_);
lean_dec_ref(v_tail_930_);
lean_dec(v_f_922_);
lean_dec_ref(v_inst_920_);
v___x_942_ = lean_apply_2(v_toPure_938_, lean_box(0), v_init_923_);
return v___x_942_;
}
else
{
size_t v___x_943_; size_t v___x_944_; lean_object* v___x_945_; 
v___x_943_ = lean_usize_of_nat(v___x_939_);
lean_dec(v___x_939_);
v___x_944_ = lean_usize_of_nat(v___x_940_);
v___x_945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_920_, v_f_922_, v_tail_930_, v___x_943_, v___x_944_, v_init_923_);
return v___x_945_;
}
}
}
else
{
lean_object* v_root_946_; lean_object* v_tail_947_; lean_object* v___f_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_inc(v_toBind_926_);
v_root_946_ = lean_ctor_get(v_t_921_, 0);
lean_inc_ref(v_root_946_);
v_tail_947_ = lean_ctor_get(v_t_921_, 1);
lean_inc_ref(v_tail_947_);
lean_dec_ref(v_t_921_);
lean_inc(v_f_922_);
lean_inc_ref(v_inst_920_);
lean_inc_ref(v_toApplicative_925_);
v___f_948_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_948_, 0, v_toApplicative_925_);
lean_closure_set(v___f_948_, 1, v_tail_947_);
lean_closure_set(v___f_948_, 2, v___x_927_);
lean_closure_set(v___f_948_, 3, v_inst_920_);
lean_closure_set(v___f_948_, 4, v_f_922_);
v___x_949_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_920_, v_f_922_, v_root_946_, v_init_923_);
v___x_950_ = lean_apply_4(v_toBind_926_, lean_box(0), lean_box(0), v___x_949_, v___f_948_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___boxed(lean_object* v_inst_951_, lean_object* v_t_952_, lean_object* v_f_953_, lean_object* v_init_954_, lean_object* v_start_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_951_, v_t_952_, v_f_953_, v_init_954_, v_start_955_);
lean_dec(v_start_955_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM(lean_object* v_00_u03b1_957_, lean_object* v_m_958_, lean_object* v_inst_959_, lean_object* v_00_u03b2_960_, lean_object* v_t_961_, lean_object* v_f_962_, lean_object* v_init_963_, lean_object* v_start_964_){
_start:
{
lean_object* v___x_965_; 
v___x_965_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_959_, v_t_961_, v_f_962_, v_init_963_, v_start_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___boxed(lean_object* v_00_u03b1_966_, lean_object* v_m_967_, lean_object* v_inst_968_, lean_object* v_00_u03b2_969_, lean_object* v_t_970_, lean_object* v_f_971_, lean_object* v_init_972_, lean_object* v_start_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_PersistentArray_foldlM(v_00_u03b1_966_, v_m_967_, v_inst_968_, v_00_u03b2_969_, v_t_970_, v_f_971_, v_init_972_, v_start_973_);
lean_dec(v_start_973_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(lean_object* v_inst_975_, lean_object* v_f_976_, lean_object* v_x_977_, lean_object* v_x_978_){
_start:
{
if (lean_obj_tag(v_x_977_) == 0)
{
lean_object* v_toApplicative_979_; lean_object* v_cs_980_; lean_object* v_toPure_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v_toApplicative_979_ = lean_ctor_get(v_inst_975_, 0);
v_cs_980_ = lean_ctor_get(v_x_977_, 0);
lean_inc_ref(v_cs_980_);
lean_dec_ref_known(v_x_977_, 1);
v_toPure_981_ = lean_ctor_get(v_toApplicative_979_, 1);
v___x_982_ = lean_array_get_size(v_cs_980_);
v___x_983_ = lean_unsigned_to_nat(0u);
v___x_984_ = lean_nat_dec_lt(v___x_983_, v___x_982_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
lean_inc(v_toPure_981_);
lean_dec_ref(v_cs_980_);
lean_dec(v_f_976_);
lean_dec_ref(v_inst_975_);
v___x_985_ = lean_apply_2(v_toPure_981_, lean_box(0), v_x_978_);
return v___x_985_;
}
else
{
lean_object* v___f_986_; size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
lean_inc_ref(v_inst_975_);
v___f_986_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_986_, 0, v_inst_975_);
lean_closure_set(v___f_986_, 1, v_f_976_);
v___x_987_ = lean_usize_of_nat(v___x_982_);
v___x_988_ = ((size_t)0ULL);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_975_, v___f_986_, v_cs_980_, v___x_987_, v___x_988_, v_x_978_);
return v___x_989_;
}
}
else
{
lean_object* v_toApplicative_990_; lean_object* v_vs_991_; lean_object* v_toPure_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_toApplicative_990_ = lean_ctor_get(v_inst_975_, 0);
v_vs_991_ = lean_ctor_get(v_x_977_, 0);
lean_inc_ref(v_vs_991_);
lean_dec_ref_known(v_x_977_, 1);
v_toPure_992_ = lean_ctor_get(v_toApplicative_990_, 1);
v___x_993_ = lean_array_get_size(v_vs_991_);
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_nat_dec_lt(v___x_994_, v___x_993_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
lean_inc(v_toPure_992_);
lean_dec_ref(v_vs_991_);
lean_dec(v_f_976_);
lean_dec_ref(v_inst_975_);
v___x_996_ = lean_apply_2(v_toPure_992_, lean_box(0), v_x_978_);
return v___x_996_;
}
else
{
size_t v___x_997_; size_t v___x_998_; lean_object* v___x_999_; 
v___x_997_ = lean_usize_of_nat(v___x_993_);
v___x_998_ = ((size_t)0ULL);
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_975_, v_f_976_, v_vs_991_, v___x_997_, v___x_998_, v_x_978_);
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0(lean_object* v_inst_1000_, lean_object* v_f_1001_, lean_object* v_c_1002_, lean_object* v_b_1003_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1000_, v_f_1001_, v_c_1002_, v_b_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux(lean_object* v_00_u03b1_1005_, lean_object* v_m_1006_, lean_object* v_00_u03b2_1007_, lean_object* v_inst_1008_, lean_object* v_f_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1008_, v_f_1009_, v_x_1010_, v_x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg___lam__0(lean_object* v_inst_1013_, lean_object* v_f_1014_, lean_object* v_root_1015_, lean_object* v_____do__lift_1016_){
_start:
{
lean_object* v___x_1017_; 
v___x_1017_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1013_, v_f_1014_, v_root_1015_, v_____do__lift_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object* v_inst_1018_, lean_object* v_t_1019_, lean_object* v_f_1020_, lean_object* v_init_1021_){
_start:
{
lean_object* v_toApplicative_1022_; lean_object* v_toBind_1023_; lean_object* v_root_1024_; lean_object* v_tail_1025_; lean_object* v_toPure_1026_; lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; 
v_toApplicative_1022_ = lean_ctor_get(v_inst_1018_, 0);
v_toBind_1023_ = lean_ctor_get(v_inst_1018_, 1);
lean_inc(v_toBind_1023_);
v_root_1024_ = lean_ctor_get(v_t_1019_, 0);
lean_inc_ref(v_root_1024_);
v_tail_1025_ = lean_ctor_get(v_t_1019_, 1);
lean_inc_ref(v_tail_1025_);
lean_dec_ref(v_t_1019_);
v_toPure_1026_ = lean_ctor_get(v_toApplicative_1022_, 1);
lean_inc(v_f_1020_);
lean_inc_ref(v_inst_1018_);
v___f_1027_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1027_, 0, v_inst_1018_);
lean_closure_set(v___f_1027_, 1, v_f_1020_);
lean_closure_set(v___f_1027_, 2, v_root_1024_);
v___x_1028_ = lean_array_get_size(v_tail_1025_);
v___x_1029_ = lean_unsigned_to_nat(0u);
v___x_1030_ = lean_nat_dec_lt(v___x_1029_, v___x_1028_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_inc(v_toPure_1026_);
lean_dec_ref(v_tail_1025_);
lean_dec(v_f_1020_);
lean_dec_ref(v_inst_1018_);
v___x_1031_ = lean_apply_2(v_toPure_1026_, lean_box(0), v_init_1021_);
v___x_1032_ = lean_apply_4(v_toBind_1023_, lean_box(0), lean_box(0), v___x_1031_, v___f_1027_);
return v___x_1032_;
}
else
{
size_t v___x_1033_; size_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1033_ = lean_usize_of_nat(v___x_1028_);
v___x_1034_ = ((size_t)0ULL);
v___x_1035_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1018_, v_f_1020_, v_tail_1025_, v___x_1033_, v___x_1034_, v_init_1021_);
v___x_1036_ = lean_apply_4(v_toBind_1023_, lean_box(0), lean_box(0), v___x_1035_, v___f_1027_);
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM(lean_object* v_00_u03b1_1037_, lean_object* v_m_1038_, lean_object* v_00_u03b2_1039_, lean_object* v_inst_1040_, lean_object* v_t_1041_, lean_object* v_f_1042_, lean_object* v_init_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_1040_, v_t_1041_, v_f_1042_, v_init_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__0(lean_object* v_toPure_1045_, lean_object* v_____s_1046_){
_start:
{
lean_object* v_fst_1047_; 
v_fst_1047_ = lean_ctor_get(v_____s_1046_, 0);
if (lean_obj_tag(v_fst_1047_) == 0)
{
lean_object* v_snd_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_snd_1048_ = lean_ctor_get(v_____s_1046_, 1);
lean_inc(v_snd_1048_);
lean_dec_ref(v_____s_1046_);
v___x_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1049_, 0, v_snd_1048_);
v___x_1050_ = lean_apply_2(v_toPure_1045_, lean_box(0), v___x_1049_);
return v___x_1050_;
}
else
{
lean_object* v_val_1051_; lean_object* v___x_1052_; 
lean_inc_ref(v_fst_1047_);
lean_dec_ref(v_____s_1046_);
v_val_1051_ = lean_ctor_get(v_fst_1047_, 0);
lean_inc(v_val_1051_);
lean_dec_ref_known(v_fst_1047_, 1);
v___x_1052_ = lean_apply_2(v_toPure_1045_, lean_box(0), v_val_1051_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__1(lean_object* v_snd_1053_, lean_object* v_toPure_1054_, lean_object* v___x_1055_, lean_object* v_____do__lift_1056_){
_start:
{
if (lean_obj_tag(v_____do__lift_1056_) == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_dec(v___x_1055_);
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v_____do__lift_1056_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_snd_1053_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
v___x_1060_ = lean_apply_2(v_toPure_1054_, lean_box(0), v___x_1059_);
return v___x_1060_;
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1070_; 
lean_dec(v_snd_1053_);
v_a_1061_ = lean_ctor_get(v_____do__lift_1056_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_____do__lift_1056_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1063_ = v_____do__lift_1056_;
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v_____do__lift_1056_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1055_);
lean_ctor_set(v___x_1065_, 1, v_a_1061_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1065_);
v___x_1067_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
lean_object* v___x_1068_; 
v___x_1068_ = lean_apply_2(v_toPure_1054_, lean_box(0), v___x_1067_);
return v___x_1068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__5(lean_object* v_toPure_1071_, lean_object* v___x_1072_, lean_object* v_f_1073_, lean_object* v_toBind_1074_, lean_object* v_a_1075_, lean_object* v_x_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_snd_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_snd_1078_ = lean_ctor_get(v___y_1077_, 1);
lean_inc_n(v_snd_1078_, 2);
lean_dec_ref(v___y_1077_);
v___f_1079_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1079_, 0, v_snd_1078_);
lean_closure_set(v___f_1079_, 1, v_toPure_1071_);
lean_closure_set(v___f_1079_, 2, v___x_1072_);
v___x_1080_ = lean_apply_2(v_f_1073_, v_a_1075_, v_snd_1078_);
v___x_1081_ = lean_apply_4(v_toBind_1074_, lean_box(0), lean_box(0), v___x_1080_, v___f_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed(lean_object* v_toPure_1082_, lean_object* v___x_1083_, lean_object* v_inst_1084_, lean_object* v_f_1085_, lean_object* v_toBind_1086_, lean_object* v_a_1087_, lean_object* v_x_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Lean_PersistentArray_forInAux___redArg___lam__2(v_toPure_1082_, v___x_1083_, v_inst_1084_, v_f_1085_, v_toBind_1086_, v_a_1087_, v_x_1088_, v___y_1089_);
lean_dec_ref(v_a_1087_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg(lean_object* v_inst_1091_, lean_object* v_f_1092_, lean_object* v_n_1093_, lean_object* v_b_1094_){
_start:
{
if (lean_obj_tag(v_n_1093_) == 0)
{
lean_object* v_toApplicative_1095_; lean_object* v_toBind_1096_; lean_object* v_toPure_1097_; lean_object* v_cs_1098_; lean_object* v___f_1099_; lean_object* v___x_1100_; lean_object* v___f_1101_; lean_object* v___x_1102_; size_t v_sz_1103_; size_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v_toApplicative_1095_ = lean_ctor_get(v_inst_1091_, 0);
v_toBind_1096_ = lean_ctor_get(v_inst_1091_, 1);
lean_inc_n(v_toBind_1096_, 2);
v_toPure_1097_ = lean_ctor_get(v_toApplicative_1095_, 1);
v_cs_1098_ = lean_ctor_get(v_n_1093_, 0);
lean_inc_n(v_toPure_1097_, 2);
v___f_1099_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1099_, 0, v_toPure_1097_);
v___x_1100_ = lean_box(0);
lean_inc_ref(v_inst_1091_);
v___f_1101_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1101_, 0, v_toPure_1097_);
lean_closure_set(v___f_1101_, 1, v___x_1100_);
lean_closure_set(v___f_1101_, 2, v_inst_1091_);
lean_closure_set(v___f_1101_, 3, v_f_1092_);
lean_closure_set(v___f_1101_, 4, v_toBind_1096_);
v___x_1102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v_b_1094_);
v_sz_1103_ = lean_array_size(v_cs_1098_);
v___x_1104_ = ((size_t)0ULL);
lean_inc_ref(v_cs_1098_);
v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1091_, v_cs_1098_, v___f_1101_, v_sz_1103_, v___x_1104_, v___x_1102_);
v___x_1106_ = lean_apply_4(v_toBind_1096_, lean_box(0), lean_box(0), v___x_1105_, v___f_1099_);
return v___x_1106_;
}
else
{
lean_object* v_toApplicative_1107_; lean_object* v_toBind_1108_; lean_object* v_toPure_1109_; lean_object* v_vs_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; lean_object* v___f_1113_; lean_object* v___x_1114_; size_t v_sz_1115_; size_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_toApplicative_1107_ = lean_ctor_get(v_inst_1091_, 0);
v_toBind_1108_ = lean_ctor_get(v_inst_1091_, 1);
lean_inc_n(v_toBind_1108_, 2);
v_toPure_1109_ = lean_ctor_get(v_toApplicative_1107_, 1);
v_vs_1110_ = lean_ctor_get(v_n_1093_, 0);
lean_inc_n(v_toPure_1109_, 2);
v___f_1111_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1111_, 0, v_toPure_1109_);
v___x_1112_ = lean_box(0);
v___f_1113_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__5), 7, 4);
lean_closure_set(v___f_1113_, 0, v_toPure_1109_);
lean_closure_set(v___f_1113_, 1, v___x_1112_);
lean_closure_set(v___f_1113_, 2, v_f_1092_);
lean_closure_set(v___f_1113_, 3, v_toBind_1108_);
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v_b_1094_);
v_sz_1115_ = lean_array_size(v_vs_1110_);
v___x_1116_ = ((size_t)0ULL);
lean_inc_ref(v_vs_1110_);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1091_, v_vs_1110_, v___f_1113_, v_sz_1115_, v___x_1116_, v___x_1114_);
v___x_1118_ = lean_apply_4(v_toBind_1108_, lean_box(0), lean_box(0), v___x_1117_, v___f_1111_);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2(lean_object* v_toPure_1119_, lean_object* v___x_1120_, lean_object* v_inst_1121_, lean_object* v_f_1122_, lean_object* v_toBind_1123_, lean_object* v_a_1124_, lean_object* v_x_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_snd_1127_; lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_snd_1127_ = lean_ctor_get(v___y_1126_, 1);
lean_inc_n(v_snd_1127_, 2);
lean_dec_ref(v___y_1126_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1128_, 0, v_snd_1127_);
lean_closure_set(v___f_1128_, 1, v_toPure_1119_);
lean_closure_set(v___f_1128_, 2, v___x_1120_);
v___x_1129_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1121_, v_f_1122_, v_a_1124_, v_snd_1127_);
v___x_1130_ = lean_apply_4(v_toBind_1123_, lean_box(0), lean_box(0), v___x_1129_, v___f_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___boxed(lean_object* v_inst_1131_, lean_object* v_f_1132_, lean_object* v_n_1133_, lean_object* v_b_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1131_, v_f_1132_, v_n_1133_, v_b_1134_);
lean_dec_ref(v_n_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux(lean_object* v_00_u03b1_1136_, lean_object* v_00_u03b2_1137_, lean_object* v_m_1138_, lean_object* v_inst_1139_, lean_object* v_inh_1140_, lean_object* v_f_1141_, lean_object* v_n_1142_, lean_object* v_b_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1139_, v_f_1141_, v_n_1142_, v_b_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___boxed(lean_object* v_00_u03b1_1145_, lean_object* v_00_u03b2_1146_, lean_object* v_m_1147_, lean_object* v_inst_1148_, lean_object* v_inh_1149_, lean_object* v_f_1150_, lean_object* v_n_1151_, lean_object* v_b_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_PersistentArray_forInAux(v_00_u03b1_1145_, v_00_u03b2_1146_, v_m_1147_, v_inst_1148_, v_inh_1149_, v_f_1150_, v_n_1151_, v_b_1152_);
lean_dec_ref(v_n_1151_);
lean_dec(v_inh_1149_);
return v_res_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__0(lean_object* v_toPure_1154_, lean_object* v_____s_1155_){
_start:
{
lean_object* v_fst_1156_; 
v_fst_1156_ = lean_ctor_get(v_____s_1155_, 0);
if (lean_obj_tag(v_fst_1156_) == 0)
{
lean_object* v_snd_1157_; lean_object* v___x_1158_; 
v_snd_1157_ = lean_ctor_get(v_____s_1155_, 1);
lean_inc(v_snd_1157_);
lean_dec_ref(v_____s_1155_);
v___x_1158_ = lean_apply_2(v_toPure_1154_, lean_box(0), v_snd_1157_);
return v___x_1158_;
}
else
{
lean_object* v_val_1159_; lean_object* v___x_1160_; 
lean_inc_ref(v_fst_1156_);
lean_dec_ref(v_____s_1155_);
v_val_1159_ = lean_ctor_get(v_fst_1156_, 0);
lean_inc(v_val_1159_);
lean_dec_ref_known(v_fst_1156_, 1);
v___x_1160_ = lean_apply_2(v_toPure_1154_, lean_box(0), v_val_1159_);
return v___x_1160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__1(lean_object* v_snd_1161_, lean_object* v_toPure_1162_, lean_object* v___x_1163_, lean_object* v_____do__lift_1164_){
_start:
{
if (lean_obj_tag(v_____do__lift_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1175_; 
lean_dec(v___x_1163_);
v_a_1165_ = lean_ctor_get(v_____do__lift_1164_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_____do__lift_1164_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1167_ = v_____do__lift_1164_;
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v_____do__lift_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v_a_1165_);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v_snd_1161_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_apply_2(v_toPure_1162_, lean_box(0), v___x_1172_);
return v___x_1173_;
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v_snd_1161_);
v_a_1176_ = lean_ctor_get(v_____do__lift_1164_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_____do__lift_1164_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1178_ = v_____do__lift_1164_;
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v_____do__lift_1164_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1163_);
lean_ctor_set(v___x_1180_, 1, v_a_1176_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1180_);
v___x_1182_ = v___x_1178_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_apply_2(v_toPure_1162_, lean_box(0), v___x_1182_);
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__2(lean_object* v_toPure_1186_, lean_object* v___x_1187_, lean_object* v_f_1188_, lean_object* v_toBind_1189_, lean_object* v_a_1190_, lean_object* v_x_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_snd_1193_; lean_object* v___f_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_snd_1193_ = lean_ctor_get(v___y_1192_, 1);
lean_inc_n(v_snd_1193_, 2);
lean_dec_ref(v___y_1192_);
v___f_1194_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1194_, 0, v_snd_1193_);
lean_closure_set(v___f_1194_, 1, v_toPure_1186_);
lean_closure_set(v___f_1194_, 2, v___x_1187_);
v___x_1195_ = lean_apply_2(v_f_1188_, v_a_1190_, v_snd_1193_);
v___x_1196_ = lean_apply_4(v_toBind_1189_, lean_box(0), lean_box(0), v___x_1195_, v___f_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__3(lean_object* v_toPure_1197_, lean_object* v_f_1198_, lean_object* v_toBind_1199_, lean_object* v_tail_1200_, lean_object* v_inst_1201_, lean_object* v___f_1202_, lean_object* v_____do__lift_1203_){
_start:
{
if (lean_obj_tag(v_____do__lift_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1205_; 
lean_dec(v___f_1202_);
lean_dec_ref(v_inst_1201_);
lean_dec_ref(v_tail_1200_);
lean_dec(v_toBind_1199_);
lean_dec(v_f_1198_);
v_a_1204_ = lean_ctor_get(v_____do__lift_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v_____do__lift_1203_, 1);
v___x_1205_ = lean_apply_2(v_toPure_1197_, lean_box(0), v_a_1204_);
return v___x_1205_;
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1207_; lean_object* v___f_1208_; lean_object* v___x_1209_; size_t v_sz_1210_; size_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_a_1206_ = lean_ctor_get(v_____do__lift_1203_, 0);
lean_inc(v_a_1206_);
lean_dec_ref_known(v_____do__lift_1203_, 1);
v___x_1207_ = lean_box(0);
lean_inc(v_toBind_1199_);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__2), 7, 4);
lean_closure_set(v___f_1208_, 0, v_toPure_1197_);
lean_closure_set(v___f_1208_, 1, v___x_1207_);
lean_closure_set(v___f_1208_, 2, v_f_1198_);
lean_closure_set(v___f_1208_, 3, v_toBind_1199_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v_a_1206_);
v_sz_1210_ = lean_array_size(v_tail_1200_);
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1201_, v_tail_1200_, v___f_1208_, v_sz_1210_, v___x_1211_, v___x_1209_);
v___x_1213_ = lean_apply_4(v_toBind_1199_, lean_box(0), lean_box(0), v___x_1212_, v___f_1202_);
return v___x_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object* v_inst_1214_, lean_object* v_t_1215_, lean_object* v_init_1216_, lean_object* v_f_1217_){
_start:
{
lean_object* v_toApplicative_1218_; lean_object* v_toBind_1219_; lean_object* v_root_1220_; lean_object* v_tail_1221_; lean_object* v_toPure_1222_; lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___f_1225_; lean_object* v___x_1226_; 
v_toApplicative_1218_ = lean_ctor_get(v_inst_1214_, 0);
v_toBind_1219_ = lean_ctor_get(v_inst_1214_, 1);
lean_inc_n(v_toBind_1219_, 2);
v_root_1220_ = lean_ctor_get(v_t_1215_, 0);
v_tail_1221_ = lean_ctor_get(v_t_1215_, 1);
v_toPure_1222_ = lean_ctor_get(v_toApplicative_1218_, 1);
lean_inc_n(v_toPure_1222_, 2);
lean_inc(v_f_1217_);
lean_inc_ref(v_inst_1214_);
v___x_1223_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1214_, v_f_1217_, v_root_1220_, v_init_1216_);
v___f_1224_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1224_, 0, v_toPure_1222_);
lean_inc_ref(v_tail_1221_);
v___f_1225_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1225_, 0, v_toPure_1222_);
lean_closure_set(v___f_1225_, 1, v_f_1217_);
lean_closure_set(v___f_1225_, 2, v_toBind_1219_);
lean_closure_set(v___f_1225_, 3, v_tail_1221_);
lean_closure_set(v___f_1225_, 4, v_inst_1214_);
lean_closure_set(v___f_1225_, 5, v___f_1224_);
v___x_1226_ = lean_apply_4(v_toBind_1219_, lean_box(0), lean_box(0), v___x_1223_, v___f_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___boxed(lean_object* v_inst_1227_, lean_object* v_t_1228_, lean_object* v_init_1229_, lean_object* v_f_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1227_, v_t_1228_, v_init_1229_, v_f_1230_);
lean_dec_ref(v_t_1228_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn(lean_object* v_00_u03b1_1232_, lean_object* v_m_1233_, lean_object* v_inst_1234_, lean_object* v_00_u03b2_1235_, lean_object* v_t_1236_, lean_object* v_init_1237_, lean_object* v_f_1238_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1234_, v_t_1236_, v_init_1237_, v_f_1238_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___boxed(lean_object* v_00_u03b1_1240_, lean_object* v_m_1241_, lean_object* v_inst_1242_, lean_object* v_00_u03b2_1243_, lean_object* v_t_1244_, lean_object* v_init_1245_, lean_object* v_f_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_PersistentArray_forIn(v_00_u03b1_1240_, v_m_1241_, v_inst_1242_, v_00_u03b2_1243_, v_t_1244_, v_init_1245_, v_f_1246_);
lean_dec_ref(v_t_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad___redArg(lean_object* v_inst_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1249_, 0, lean_box(0));
lean_closure_set(v___x_1249_, 1, lean_box(0));
lean_closure_set(v___x_1249_, 2, v_inst_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad(lean_object* v_00_u03b1_1250_, lean_object* v_m_1251_, lean_object* v_inst_1252_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1253_, 0, lean_box(0));
lean_closure_set(v___x_1253_, 1, lean_box(0));
lean_closure_set(v___x_1253_, 2, v_inst_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(lean_object* v_toPure_1254_, lean_object* v_____s_1255_){
_start:
{
lean_object* v_fst_1256_; 
v_fst_1256_ = lean_ctor_get(v_____s_1255_, 0);
lean_inc(v_fst_1256_);
lean_dec_ref(v_____s_1255_);
if (lean_obj_tag(v_fst_1256_) == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_apply_2(v_toPure_1254_, lean_box(0), v___x_1257_);
return v___x_1258_;
}
else
{
lean_object* v_val_1259_; lean_object* v___x_1260_; 
v_val_1259_ = lean_ctor_get(v_fst_1256_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v_fst_1256_, 1);
v___x_1260_ = lean_apply_2(v_toPure_1254_, lean_box(0), v_val_1259_);
return v___x_1260_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(lean_object* v___x_1261_, lean_object* v_toPure_1262_, lean_object* v___x_1263_, lean_object* v_____do__lift_1264_){
_start:
{
if (lean_obj_tag(v_____do__lift_1264_) == 1)
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
lean_dec_ref(v___x_1263_);
v___x_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1265_, 0, v_____do__lift_1264_);
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
lean_ctor_set(v___x_1266_, 1, v___x_1261_);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
v___x_1268_ = lean_apply_2(v_toPure_1262_, lean_box(0), v___x_1267_);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
lean_dec(v_____do__lift_1264_);
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1263_);
v___x_1270_ = lean_apply_2(v_toPure_1262_, lean_box(0), v___x_1269_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(lean_object* v_f_1271_, lean_object* v_toBind_1272_, lean_object* v___f_1273_, lean_object* v_a_1274_, lean_object* v_x_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_apply_1(v_f_1271_, v_a_1274_);
v___x_1278_ = lean_apply_4(v_toBind_1272_, lean_box(0), lean_box(0), v___x_1277_, v___f_1273_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(lean_object* v_f_1279_, lean_object* v_toBind_1280_, lean_object* v___f_1281_, lean_object* v_a_1282_, lean_object* v_x_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(v_f_1279_, v_toBind_1280_, v___f_1281_, v_a_1282_, v_x_1283_, v___y_1284_);
lean_dec_ref(v___y_1284_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(lean_object* v_inst_1289_, lean_object* v_f_1290_, lean_object* v_toBind_1291_, lean_object* v___f_1292_, lean_object* v_a_1293_, lean_object* v_x_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(v_inst_1289_, v_f_1290_, v_toBind_1291_, v___f_1292_, v_a_1293_, v_x_1294_, v___y_1295_);
lean_dec_ref(v___y_1295_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg(lean_object* v_inst_1297_, lean_object* v_f_1298_, lean_object* v_x_1299_){
_start:
{
if (lean_obj_tag(v_x_1299_) == 0)
{
lean_object* v_toApplicative_1300_; lean_object* v_cs_1301_; lean_object* v_toBind_1302_; lean_object* v_toPure_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___f_1306_; lean_object* v___f_1307_; lean_object* v___f_1308_; size_t v_sz_1309_; size_t v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; 
v_toApplicative_1300_ = lean_ctor_get(v_inst_1297_, 0);
v_cs_1301_ = lean_ctor_get(v_x_1299_, 0);
lean_inc_ref(v_cs_1301_);
lean_dec_ref_known(v_x_1299_, 1);
v_toBind_1302_ = lean_ctor_get(v_inst_1297_, 1);
lean_inc_n(v_toBind_1302_, 2);
v_toPure_1303_ = lean_ctor_get(v_toApplicative_1300_, 1);
v___x_1304_ = lean_box(0);
v___x_1305_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1303_, 2);
v___f_1306_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1306_, 0, v_toPure_1303_);
v___f_1307_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1307_, 0, v___x_1304_);
lean_closure_set(v___f_1307_, 1, v_toPure_1303_);
lean_closure_set(v___f_1307_, 2, v___x_1305_);
lean_inc_ref(v_inst_1297_);
v___f_1308_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1308_, 0, v_inst_1297_);
lean_closure_set(v___f_1308_, 1, v_f_1298_);
lean_closure_set(v___f_1308_, 2, v_toBind_1302_);
lean_closure_set(v___f_1308_, 3, v___f_1307_);
v_sz_1309_ = lean_array_size(v_cs_1301_);
v___x_1310_ = ((size_t)0ULL);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1297_, v_cs_1301_, v___f_1308_, v_sz_1309_, v___x_1310_, v___x_1305_);
v___x_1312_ = lean_apply_4(v_toBind_1302_, lean_box(0), lean_box(0), v___x_1311_, v___f_1306_);
return v___x_1312_;
}
else
{
lean_object* v_toApplicative_1313_; lean_object* v_vs_1314_; lean_object* v_toBind_1315_; lean_object* v_toPure_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___f_1319_; lean_object* v___f_1320_; lean_object* v___f_1321_; size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
v_toApplicative_1313_ = lean_ctor_get(v_inst_1297_, 0);
v_vs_1314_ = lean_ctor_get(v_x_1299_, 0);
lean_inc_ref(v_vs_1314_);
lean_dec_ref_known(v_x_1299_, 1);
v_toBind_1315_ = lean_ctor_get(v_inst_1297_, 1);
lean_inc_n(v_toBind_1315_, 2);
v_toPure_1316_ = lean_ctor_get(v_toApplicative_1313_, 1);
v___x_1317_ = lean_box(0);
v___x_1318_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1316_, 2);
v___f_1319_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1319_, 0, v_toPure_1316_);
v___f_1320_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1320_, 0, v___x_1317_);
lean_closure_set(v___f_1320_, 1, v_toPure_1316_);
lean_closure_set(v___f_1320_, 2, v___x_1318_);
v___f_1321_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1321_, 0, v_f_1298_);
lean_closure_set(v___f_1321_, 1, v_toBind_1315_);
lean_closure_set(v___f_1321_, 2, v___f_1320_);
v_sz_1322_ = lean_array_size(v_vs_1314_);
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1297_, v_vs_1314_, v___f_1321_, v_sz_1322_, v___x_1323_, v___x_1318_);
v___x_1325_ = lean_apply_4(v_toBind_1315_, lean_box(0), lean_box(0), v___x_1324_, v___f_1319_);
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(lean_object* v_inst_1326_, lean_object* v_f_1327_, lean_object* v_toBind_1328_, lean_object* v___f_1329_, lean_object* v_a_1330_, lean_object* v_x_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1333_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1326_, v_f_1327_, v_a_1330_);
v___x_1334_ = lean_apply_4(v_toBind_1328_, lean_box(0), lean_box(0), v___x_1333_, v___f_1329_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux(lean_object* v_00_u03b1_1335_, lean_object* v_m_1336_, lean_object* v_inst_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_f_1339_, lean_object* v_x_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1337_, v_f_1339_, v_x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(lean_object* v_toPure_1342_, lean_object* v_____do__lift_1343_, lean_object* v_____s_1344_){
_start:
{
lean_object* v_fst_1345_; 
v_fst_1345_ = lean_ctor_get(v_____s_1344_, 0);
lean_inc(v_fst_1345_);
lean_dec_ref(v_____s_1344_);
if (lean_obj_tag(v_fst_1345_) == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_apply_2(v_toPure_1342_, lean_box(0), v_____do__lift_1343_);
return v___x_1346_;
}
else
{
lean_object* v_val_1347_; lean_object* v___x_1348_; 
lean_dec(v_____do__lift_1343_);
v_val_1347_ = lean_ctor_get(v_fst_1345_, 0);
lean_inc(v_val_1347_);
lean_dec_ref_known(v_fst_1345_, 1);
v___x_1348_ = lean_apply_2(v_toPure_1342_, lean_box(0), v_val_1347_);
return v___x_1348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(lean_object* v___x_1349_, lean_object* v_toPure_1350_, lean_object* v___x_1351_, lean_object* v_____do__lift_1352_){
_start:
{
if (lean_obj_tag(v_____do__lift_1352_) == 1)
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; 
lean_dec_ref(v___x_1351_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_____do__lift_1352_);
v___x_1354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v___x_1349_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
v___x_1356_ = lean_apply_2(v_toPure_1350_, lean_box(0), v___x_1355_);
return v___x_1356_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v_____do__lift_1352_);
v___x_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1351_);
v___x_1358_ = lean_apply_2(v_toPure_1350_, lean_box(0), v___x_1357_);
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1359_, lean_object* v_toBind_1360_, lean_object* v___f_1361_, lean_object* v_a_1362_, lean_object* v_x_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___x_1365_ = lean_apply_1(v_f_1359_, v_a_1362_);
v___x_1366_ = lean_apply_4(v_toBind_1360_, lean_box(0), lean_box(0), v___x_1365_, v___f_1361_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1367_, lean_object* v_toBind_1368_, lean_object* v___f_1369_, lean_object* v_a_1370_, lean_object* v_x_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(v_f_1367_, v_toBind_1368_, v___f_1369_, v_a_1370_, v_x_1371_, v___y_1372_);
lean_dec_ref(v___y_1372_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(lean_object* v_toPure_1374_, lean_object* v_f_1375_, lean_object* v_toBind_1376_, lean_object* v_tail_1377_, lean_object* v_inst_1378_, lean_object* v_____do__lift_1379_){
_start:
{
if (lean_obj_tag(v_____do__lift_1379_) == 0)
{
lean_object* v___f_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___f_1383_; lean_object* v___f_1384_; size_t v_sz_1385_; size_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_inc(v_toPure_1374_);
v___f_1380_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1380_, 0, v_toPure_1374_);
lean_closure_set(v___f_1380_, 1, v_____do__lift_1379_);
v___x_1381_ = lean_box(0);
v___x_1382_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
v___f_1383_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1383_, 0, v___x_1381_);
lean_closure_set(v___f_1383_, 1, v_toPure_1374_);
lean_closure_set(v___f_1383_, 2, v___x_1382_);
lean_inc(v_toBind_1376_);
v___f_1384_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1384_, 0, v_f_1375_);
lean_closure_set(v___f_1384_, 1, v_toBind_1376_);
lean_closure_set(v___f_1384_, 2, v___f_1383_);
v_sz_1385_ = lean_array_size(v_tail_1377_);
v___x_1386_ = ((size_t)0ULL);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1378_, v_tail_1377_, v___f_1384_, v_sz_1385_, v___x_1386_, v___x_1382_);
v___x_1388_ = lean_apply_4(v_toBind_1376_, lean_box(0), lean_box(0), v___x_1387_, v___f_1380_);
return v___x_1388_;
}
else
{
lean_object* v___x_1389_; 
lean_dec_ref(v_inst_1378_);
lean_dec_ref(v_tail_1377_);
lean_dec(v_toBind_1376_);
lean_dec(v_f_1375_);
v___x_1389_ = lean_apply_2(v_toPure_1374_, lean_box(0), v_____do__lift_1379_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object* v_inst_1390_, lean_object* v_t_1391_, lean_object* v_f_1392_){
_start:
{
lean_object* v_toApplicative_1393_; lean_object* v_toBind_1394_; lean_object* v_root_1395_; lean_object* v_tail_1396_; lean_object* v_toPure_1397_; lean_object* v___x_1398_; lean_object* v___f_1399_; lean_object* v___x_1400_; 
v_toApplicative_1393_ = lean_ctor_get(v_inst_1390_, 0);
v_toBind_1394_ = lean_ctor_get(v_inst_1390_, 1);
lean_inc_n(v_toBind_1394_, 2);
v_root_1395_ = lean_ctor_get(v_t_1391_, 0);
lean_inc_ref(v_root_1395_);
v_tail_1396_ = lean_ctor_get(v_t_1391_, 1);
lean_inc_ref(v_tail_1396_);
lean_dec_ref(v_t_1391_);
v_toPure_1397_ = lean_ctor_get(v_toApplicative_1393_, 1);
lean_inc(v_toPure_1397_);
lean_inc(v_f_1392_);
lean_inc_ref(v_inst_1390_);
v___x_1398_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1390_, v_f_1392_, v_root_1395_);
v___f_1399_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1399_, 0, v_toPure_1397_);
lean_closure_set(v___f_1399_, 1, v_f_1392_);
lean_closure_set(v___f_1399_, 2, v_toBind_1394_);
lean_closure_set(v___f_1399_, 3, v_tail_1396_);
lean_closure_set(v___f_1399_, 4, v_inst_1390_);
v___x_1400_ = lean_apply_4(v_toBind_1394_, lean_box(0), lean_box(0), v___x_1398_, v___f_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f(lean_object* v_00_u03b1_1401_, lean_object* v_m_1402_, lean_object* v_inst_1403_, lean_object* v_00_u03b2_1404_, lean_object* v_t_1405_, lean_object* v_f_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_1403_, v_t_1405_, v_f_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg(lean_object* v_inst_1408_, lean_object* v_f_1409_, lean_object* v_x_1410_){
_start:
{
if (lean_obj_tag(v_x_1410_) == 0)
{
lean_object* v_cs_1411_; lean_object* v___f_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v_cs_1411_ = lean_ctor_get(v_x_1410_, 0);
lean_inc_ref(v_cs_1411_);
lean_dec_ref_known(v_x_1410_, 1);
lean_inc_ref(v_inst_1408_);
v___f_1412_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1412_, 0, v_inst_1408_);
lean_closure_set(v___f_1412_, 1, v_f_1409_);
v___x_1413_ = lean_array_get_size(v_cs_1411_);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1408_, v___f_1412_, v_cs_1411_, v___x_1413_, lean_box(0));
return v___x_1414_;
}
else
{
lean_object* v_vs_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v_vs_1415_ = lean_ctor_get(v_x_1410_, 0);
lean_inc_ref(v_vs_1415_);
lean_dec_ref_known(v_x_1410_, 1);
v___x_1416_ = lean_array_get_size(v_vs_1415_);
v___x_1417_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1408_, v_f_1409_, v_vs_1415_, v___x_1416_, lean_box(0));
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(lean_object* v_inst_1418_, lean_object* v_f_1419_, lean_object* v_c_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1418_, v_f_1419_, v_c_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux(lean_object* v_00_u03b1_1422_, lean_object* v_m_1423_, lean_object* v_inst_1424_, lean_object* v_00_u03b2_1425_, lean_object* v_f_1426_, lean_object* v_x_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1424_, v_f_1426_, v_x_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(lean_object* v_inst_1429_, lean_object* v_f_1430_, lean_object* v_root_1431_, lean_object* v_toPure_1432_, lean_object* v_____do__lift_1433_){
_start:
{
if (lean_obj_tag(v_____do__lift_1433_) == 0)
{
lean_object* v___x_1434_; 
lean_dec(v_toPure_1432_);
v___x_1434_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1429_, v_f_1430_, v_root_1431_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; 
lean_dec_ref(v_root_1431_);
lean_dec(v_f_1430_);
lean_dec_ref(v_inst_1429_);
v___x_1435_ = lean_apply_2(v_toPure_1432_, lean_box(0), v_____do__lift_1433_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object* v_inst_1436_, lean_object* v_t_1437_, lean_object* v_f_1438_){
_start:
{
lean_object* v_toApplicative_1439_; lean_object* v_toBind_1440_; lean_object* v_root_1441_; lean_object* v_tail_1442_; lean_object* v_toPure_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; 
v_toApplicative_1439_ = lean_ctor_get(v_inst_1436_, 0);
v_toBind_1440_ = lean_ctor_get(v_inst_1436_, 1);
lean_inc(v_toBind_1440_);
v_root_1441_ = lean_ctor_get(v_t_1437_, 0);
lean_inc_ref(v_root_1441_);
v_tail_1442_ = lean_ctor_get(v_t_1437_, 1);
lean_inc_ref(v_tail_1442_);
lean_dec_ref(v_t_1437_);
v_toPure_1443_ = lean_ctor_get(v_toApplicative_1439_, 1);
lean_inc(v_toPure_1443_);
v___x_1444_ = lean_array_get_size(v_tail_1442_);
lean_inc(v_f_1438_);
lean_inc_ref(v_inst_1436_);
v___x_1445_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1436_, v_f_1438_, v_tail_1442_, v___x_1444_, lean_box(0));
v___f_1446_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1446_, 0, v_inst_1436_);
lean_closure_set(v___f_1446_, 1, v_f_1438_);
lean_closure_set(v___f_1446_, 2, v_root_1441_);
lean_closure_set(v___f_1446_, 3, v_toPure_1443_);
v___x_1447_ = lean_apply_4(v_toBind_1440_, lean_box(0), lean_box(0), v___x_1445_, v___f_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f(lean_object* v_00_u03b1_1448_, lean_object* v_m_1449_, lean_object* v_inst_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_t_1452_, lean_object* v_f_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_1450_, v_t_1452_, v_f_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__1(lean_object* v_f_1455_, lean_object* v_x_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1458_; 
v___x_1458_ = lean_apply_1(v_f_1455_, v___y_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg(lean_object* v_inst_1459_, lean_object* v_f_1460_, lean_object* v_x_1461_){
_start:
{
if (lean_obj_tag(v_x_1461_) == 0)
{
lean_object* v_toApplicative_1462_; lean_object* v_cs_1463_; lean_object* v_toPure_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_toApplicative_1462_ = lean_ctor_get(v_inst_1459_, 0);
v_cs_1463_ = lean_ctor_get(v_x_1461_, 0);
lean_inc_ref(v_cs_1463_);
lean_dec_ref_known(v_x_1461_, 1);
v_toPure_1464_ = lean_ctor_get(v_toApplicative_1462_, 1);
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = lean_array_get_size(v_cs_1463_);
v___x_1467_ = lean_box(0);
v___x_1468_ = lean_nat_dec_lt(v___x_1465_, v___x_1466_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
lean_inc(v_toPure_1464_);
lean_dec_ref(v_cs_1463_);
lean_dec(v_f_1460_);
lean_dec_ref(v_inst_1459_);
v___x_1469_ = lean_apply_2(v_toPure_1464_, lean_box(0), v___x_1467_);
return v___x_1469_;
}
else
{
lean_object* v___f_1470_; size_t v___x_1471_; size_t v___x_1472_; lean_object* v___x_1473_; 
lean_inc_ref(v_inst_1459_);
v___f_1470_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1470_, 0, v_inst_1459_);
lean_closure_set(v___f_1470_, 1, v_f_1460_);
v___x_1471_ = ((size_t)0ULL);
v___x_1472_ = lean_usize_of_nat(v___x_1466_);
v___x_1473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1459_, v___f_1470_, v_cs_1463_, v___x_1471_, v___x_1472_, v___x_1467_);
return v___x_1473_;
}
}
else
{
lean_object* v_toApplicative_1474_; lean_object* v_vs_1475_; lean_object* v_toPure_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; uint8_t v___x_1480_; 
v_toApplicative_1474_ = lean_ctor_get(v_inst_1459_, 0);
v_vs_1475_ = lean_ctor_get(v_x_1461_, 0);
lean_inc_ref(v_vs_1475_);
lean_dec_ref_known(v_x_1461_, 1);
v_toPure_1476_ = lean_ctor_get(v_toApplicative_1474_, 1);
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_array_get_size(v_vs_1475_);
v___x_1479_ = lean_box(0);
v___x_1480_ = lean_nat_dec_lt(v___x_1477_, v___x_1478_);
if (v___x_1480_ == 0)
{
lean_object* v___x_1481_; 
lean_inc(v_toPure_1476_);
lean_dec_ref(v_vs_1475_);
lean_dec(v_f_1460_);
lean_dec_ref(v_inst_1459_);
v___x_1481_ = lean_apply_2(v_toPure_1476_, lean_box(0), v___x_1479_);
return v___x_1481_;
}
else
{
lean_object* v___f_1482_; size_t v___x_1483_; size_t v___x_1484_; lean_object* v___x_1485_; 
v___f_1482_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1482_, 0, v_f_1460_);
v___x_1483_ = ((size_t)0ULL);
v___x_1484_ = lean_usize_of_nat(v___x_1478_);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1459_, v___f_1482_, v_vs_1475_, v___x_1483_, v___x_1484_, v___x_1479_);
return v___x_1485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__0(lean_object* v_inst_1486_, lean_object* v_f_1487_, lean_object* v_x_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1486_, v_f_1487_, v___y_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux(lean_object* v_00_u03b1_1491_, lean_object* v_m_1492_, lean_object* v_inst_1493_, lean_object* v_f_1494_, lean_object* v_x_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1493_, v_f_1494_, v_x_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__0(lean_object* v_f_1497_, lean_object* v_x_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = lean_apply_1(v_f_1497_, v___y_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__1(lean_object* v_tail_1501_, lean_object* v_toPure_1502_, lean_object* v_inst_1503_, lean_object* v___f_1504_, lean_object* v_x_1505_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; uint8_t v___x_1509_; 
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = lean_array_get_size(v_tail_1501_);
v___x_1508_ = lean_box(0);
v___x_1509_ = lean_nat_dec_lt(v___x_1506_, v___x_1507_);
if (v___x_1509_ == 0)
{
lean_object* v___x_1510_; 
lean_dec(v___f_1504_);
lean_dec_ref(v_inst_1503_);
lean_dec_ref(v_tail_1501_);
v___x_1510_ = lean_apply_2(v_toPure_1502_, lean_box(0), v___x_1508_);
return v___x_1510_;
}
else
{
size_t v___x_1511_; size_t v___x_1512_; lean_object* v___x_1513_; 
lean_dec(v_toPure_1502_);
v___x_1511_ = ((size_t)0ULL);
v___x_1512_ = lean_usize_of_nat(v___x_1507_);
v___x_1513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1503_, v___f_1504_, v_tail_1501_, v___x_1511_, v___x_1512_, v___x_1508_);
return v___x_1513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg(lean_object* v_inst_1514_, lean_object* v_t_1515_, lean_object* v_f_1516_){
_start:
{
lean_object* v_toApplicative_1517_; lean_object* v_toPure_1518_; lean_object* v_toSeqRight_1519_; lean_object* v_root_1520_; lean_object* v_tail_1521_; lean_object* v___f_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_toApplicative_1517_ = lean_ctor_get(v_inst_1514_, 0);
v_toPure_1518_ = lean_ctor_get(v_toApplicative_1517_, 1);
v_toSeqRight_1519_ = lean_ctor_get(v_toApplicative_1517_, 4);
lean_inc(v_toSeqRight_1519_);
v_root_1520_ = lean_ctor_get(v_t_1515_, 0);
lean_inc_ref(v_root_1520_);
v_tail_1521_ = lean_ctor_get(v_t_1515_, 1);
lean_inc_ref(v_tail_1521_);
lean_dec_ref(v_t_1515_);
lean_inc(v_f_1516_);
v___f_1522_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1522_, 0, v_f_1516_);
lean_inc_ref(v_inst_1514_);
lean_inc(v_toPure_1518_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1523_, 0, v_tail_1521_);
lean_closure_set(v___f_1523_, 1, v_toPure_1518_);
lean_closure_set(v___f_1523_, 2, v_inst_1514_);
lean_closure_set(v___f_1523_, 3, v___f_1522_);
v___x_1524_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1514_, v_f_1516_, v_root_1520_);
v___x_1525_ = lean_apply_4(v_toSeqRight_1519_, lean_box(0), lean_box(0), v___x_1524_, v___f_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0(lean_object* v_00_u03b1_1526_, lean_object* v_m_1527_, lean_object* v_inst_1528_, lean_object* v_t_1529_, lean_object* v_f_1530_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1528_, v_t_1529_, v_f_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(lean_object* v_toApplicative_1532_, lean_object* v_j_1533_, lean_object* v_cs_1534_, lean_object* v_inst_1535_, lean_object* v___f_1536_, lean_object* v_____r_1537_){
_start:
{
lean_object* v_toPure_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; uint8_t v___x_1543_; 
v_toPure_1538_ = lean_ctor_get(v_toApplicative_1532_, 1);
lean_inc(v_toPure_1538_);
lean_dec_ref(v_toApplicative_1532_);
v___x_1539_ = lean_unsigned_to_nat(1u);
v___x_1540_ = lean_nat_add(v_j_1533_, v___x_1539_);
v___x_1541_ = lean_array_get_size(v_cs_1534_);
v___x_1542_ = lean_box(0);
v___x_1543_ = lean_nat_dec_lt(v___x_1540_, v___x_1541_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; 
lean_dec(v___x_1540_);
lean_dec(v___f_1536_);
lean_dec_ref(v_inst_1535_);
lean_dec_ref(v_cs_1534_);
v___x_1544_ = lean_apply_2(v_toPure_1538_, lean_box(0), v___x_1542_);
return v___x_1544_;
}
else
{
size_t v___x_1545_; size_t v___x_1546_; lean_object* v___x_1547_; 
lean_dec(v_toPure_1538_);
v___x_1545_ = lean_usize_of_nat(v___x_1540_);
lean_dec(v___x_1540_);
v___x_1546_ = lean_usize_of_nat(v___x_1541_);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1535_, v___f_1536_, v_cs_1534_, v___x_1545_, v___x_1546_, v___x_1542_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_1548_, lean_object* v_j_1549_, lean_object* v_cs_1550_, lean_object* v_inst_1551_, lean_object* v___f_1552_, lean_object* v_____r_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(v_toApplicative_1548_, v_j_1549_, v_cs_1550_, v_inst_1551_, v___f_1552_, v_____r_1553_);
lean_dec(v_j_1549_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(lean_object* v_inst_1555_, lean_object* v_f_1556_, lean_object* v_x_1557_, size_t v_x_1558_, size_t v_x_1559_){
_start:
{
if (lean_obj_tag(v_x_1557_) == 0)
{
lean_object* v_toApplicative_1560_; lean_object* v_toBind_1561_; lean_object* v_cs_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; size_t v___x_1565_; lean_object* v_j_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; size_t v___x_1569_; size_t v___x_1570_; size_t v___x_1571_; size_t v___x_1572_; size_t v___x_1573_; size_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v_toApplicative_1560_ = lean_ctor_get(v_inst_1555_, 0);
v_toBind_1561_ = lean_ctor_get(v_inst_1555_, 1);
lean_inc(v_toBind_1561_);
v_cs_1562_ = lean_ctor_get(v_x_1557_, 0);
lean_inc_ref_n(v_cs_1562_, 2);
lean_dec_ref_known(v_x_1557_, 1);
lean_inc(v_f_1556_);
lean_inc_ref_n(v_inst_1555_, 2);
v___f_1563_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1563_, 0, v_inst_1555_);
lean_closure_set(v___f_1563_, 1, v_f_1556_);
v___x_1564_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_1565_ = lean_usize_shift_right(v_x_1558_, v_x_1559_);
v_j_1566_ = lean_usize_to_nat(v___x_1565_);
lean_inc(v_j_1566_);
lean_inc_ref(v_toApplicative_1560_);
v___f_1567_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1567_, 0, v_toApplicative_1560_);
lean_closure_set(v___f_1567_, 1, v_j_1566_);
lean_closure_set(v___f_1567_, 2, v_cs_1562_);
lean_closure_set(v___f_1567_, 3, v_inst_1555_);
lean_closure_set(v___f_1567_, 4, v___f_1563_);
v___x_1568_ = lean_array_get(v___x_1564_, v_cs_1562_, v_j_1566_);
lean_dec(v_j_1566_);
lean_dec_ref(v_cs_1562_);
v___x_1569_ = ((size_t)1ULL);
v___x_1570_ = lean_usize_shift_left(v___x_1569_, v_x_1559_);
v___x_1571_ = lean_usize_sub(v___x_1570_, v___x_1569_);
v___x_1572_ = lean_usize_land(v_x_1558_, v___x_1571_);
v___x_1573_ = ((size_t)5ULL);
v___x_1574_ = lean_usize_sub(v_x_1559_, v___x_1573_);
v___x_1575_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1555_, v_f_1556_, v___x_1568_, v___x_1572_, v___x_1574_);
v___x_1576_ = lean_apply_4(v_toBind_1561_, lean_box(0), lean_box(0), v___x_1575_, v___f_1567_);
return v___x_1576_;
}
else
{
lean_object* v_toApplicative_1577_; lean_object* v_vs_1578_; lean_object* v_toPure_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; 
v_toApplicative_1577_ = lean_ctor_get(v_inst_1555_, 0);
v_vs_1578_ = lean_ctor_get(v_x_1557_, 0);
lean_inc_ref(v_vs_1578_);
lean_dec_ref_known(v_x_1557_, 1);
v_toPure_1579_ = lean_ctor_get(v_toApplicative_1577_, 1);
v___x_1580_ = lean_usize_to_nat(v_x_1558_);
v___x_1581_ = lean_array_get_size(v_vs_1578_);
v___x_1582_ = lean_box(0);
v___x_1583_ = lean_nat_dec_lt(v___x_1580_, v___x_1581_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1584_; 
lean_inc(v_toPure_1579_);
lean_dec(v___x_1580_);
lean_dec_ref(v_vs_1578_);
lean_dec(v_f_1556_);
lean_dec_ref(v_inst_1555_);
v___x_1584_ = lean_apply_2(v_toPure_1579_, lean_box(0), v___x_1582_);
return v___x_1584_;
}
else
{
lean_object* v___f_1585_; size_t v___x_1586_; size_t v___x_1587_; lean_object* v___x_1588_; 
v___f_1585_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1585_, 0, v_f_1556_);
v___x_1586_ = lean_usize_of_nat(v___x_1580_);
lean_dec(v___x_1580_);
v___x_1587_ = lean_usize_of_nat(v___x_1581_);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1555_, v___f_1585_, v_vs_1578_, v___x_1586_, v___x_1587_, v___x_1582_);
return v___x_1588_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___boxed(lean_object* v_inst_1589_, lean_object* v_f_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_){
_start:
{
size_t v_x_257__boxed_1594_; size_t v_x_258__boxed_1595_; lean_object* v_res_1596_; 
v_x_257__boxed_1594_ = lean_unbox_usize(v_x_1592_);
lean_dec(v_x_1592_);
v_x_258__boxed_1595_ = lean_unbox_usize(v_x_1593_);
lean_dec(v_x_1593_);
v_res_1596_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1589_, v_f_1590_, v_x_1591_, v_x_257__boxed_1594_, v_x_258__boxed_1595_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(lean_object* v_00_u03b1_1597_, lean_object* v_m_1598_, lean_object* v_inst_1599_, lean_object* v_f_1600_, lean_object* v_x_1601_, size_t v_x_1602_, size_t v_x_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1599_, v_f_1600_, v_x_1601_, v_x_1602_, v_x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___boxed(lean_object* v_00_u03b1_1605_, lean_object* v_m_1606_, lean_object* v_inst_1607_, lean_object* v_f_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_, lean_object* v_x_1611_){
_start:
{
size_t v_x_317__boxed_1612_; size_t v_x_318__boxed_1613_; lean_object* v_res_1614_; 
v_x_317__boxed_1612_ = lean_unbox_usize(v_x_1610_);
lean_dec(v_x_1610_);
v_x_318__boxed_1613_ = lean_unbox_usize(v_x_1611_);
lean_dec(v_x_1611_);
v_res_1614_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(v_00_u03b1_1605_, v_m_1606_, v_inst_1607_, v_f_1608_, v_x_1609_, v_x_317__boxed_1612_, v_x_318__boxed_1613_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1(lean_object* v_toApplicative_1615_, lean_object* v_tail_1616_, lean_object* v___x_1617_, lean_object* v_inst_1618_, lean_object* v___f_1619_, lean_object* v_____r_1620_){
_start:
{
lean_object* v_toPure_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v_toPure_1621_ = lean_ctor_get(v_toApplicative_1615_, 1);
lean_inc(v_toPure_1621_);
lean_dec_ref(v_toApplicative_1615_);
v___x_1622_ = lean_array_get_size(v_tail_1616_);
v___x_1623_ = lean_box(0);
v___x_1624_ = lean_nat_dec_lt(v___x_1617_, v___x_1622_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; 
lean_dec(v___f_1619_);
lean_dec_ref(v_inst_1618_);
lean_dec_ref(v_tail_1616_);
v___x_1625_ = lean_apply_2(v_toPure_1621_, lean_box(0), v___x_1623_);
return v___x_1625_;
}
else
{
size_t v___x_1626_; size_t v___x_1627_; lean_object* v___x_1628_; 
lean_dec(v_toPure_1621_);
v___x_1626_ = ((size_t)0ULL);
v___x_1627_ = lean_usize_of_nat(v___x_1622_);
v___x_1628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1618_, v___f_1619_, v_tail_1616_, v___x_1626_, v___x_1627_, v___x_1623_);
return v___x_1628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1___boxed(lean_object* v_toApplicative_1629_, lean_object* v_tail_1630_, lean_object* v___x_1631_, lean_object* v_inst_1632_, lean_object* v___f_1633_, lean_object* v_____r_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_PersistentArray_forM___redArg___lam__1(v_toApplicative_1629_, v_tail_1630_, v___x_1631_, v_inst_1632_, v___f_1633_, v_____r_1634_);
lean_dec(v___x_1631_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg(lean_object* v_inst_1636_, lean_object* v_t_1637_, lean_object* v_f_1638_, lean_object* v_start_1639_){
_start:
{
lean_object* v_toApplicative_1640_; lean_object* v_toBind_1641_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v_toApplicative_1640_ = lean_ctor_get(v_inst_1636_, 0);
v_toBind_1641_ = lean_ctor_get(v_inst_1636_, 1);
v___x_1642_ = lean_unsigned_to_nat(0u);
v___x_1643_ = lean_nat_dec_eq(v_start_1639_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v_root_1644_; lean_object* v_tail_1645_; size_t v_shift_1646_; lean_object* v_tailOff_1647_; uint8_t v___x_1648_; 
v_root_1644_ = lean_ctor_get(v_t_1637_, 0);
lean_inc_ref(v_root_1644_);
v_tail_1645_ = lean_ctor_get(v_t_1637_, 1);
lean_inc_ref(v_tail_1645_);
v_shift_1646_ = lean_ctor_get_usize(v_t_1637_, 4);
v_tailOff_1647_ = lean_ctor_get(v_t_1637_, 3);
lean_inc(v_tailOff_1647_);
lean_dec_ref(v_t_1637_);
v___x_1648_ = lean_nat_dec_le(v_tailOff_1647_, v_start_1639_);
if (v___x_1648_ == 0)
{
lean_object* v___f_1649_; lean_object* v___f_1650_; size_t v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_inc(v_toBind_1641_);
lean_dec(v_tailOff_1647_);
lean_inc(v_f_1638_);
v___f_1649_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1649_, 0, v_f_1638_);
lean_inc_ref(v_inst_1636_);
lean_inc_ref(v_toApplicative_1640_);
v___f_1650_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1650_, 0, v_toApplicative_1640_);
lean_closure_set(v___f_1650_, 1, v_tail_1645_);
lean_closure_set(v___f_1650_, 2, v___x_1642_);
lean_closure_set(v___f_1650_, 3, v_inst_1636_);
lean_closure_set(v___f_1650_, 4, v___f_1649_);
v___x_1651_ = lean_usize_of_nat(v_start_1639_);
v___x_1652_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1636_, v_f_1638_, v_root_1644_, v___x_1651_, v_shift_1646_);
v___x_1653_ = lean_apply_4(v_toBind_1641_, lean_box(0), lean_box(0), v___x_1652_, v___f_1650_);
return v___x_1653_;
}
else
{
lean_object* v_toPure_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint8_t v___x_1658_; 
lean_dec_ref(v_root_1644_);
v_toPure_1654_ = lean_ctor_get(v_toApplicative_1640_, 1);
v___x_1655_ = lean_nat_sub(v_start_1639_, v_tailOff_1647_);
lean_dec(v_tailOff_1647_);
v___x_1656_ = lean_array_get_size(v_tail_1645_);
v___x_1657_ = lean_box(0);
v___x_1658_ = lean_nat_dec_lt(v___x_1655_, v___x_1656_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; 
lean_inc(v_toPure_1654_);
lean_dec(v___x_1655_);
lean_dec_ref(v_tail_1645_);
lean_dec(v_f_1638_);
lean_dec_ref(v_inst_1636_);
v___x_1659_ = lean_apply_2(v_toPure_1654_, lean_box(0), v___x_1657_);
return v___x_1659_;
}
else
{
lean_object* v___f_1660_; size_t v___x_1661_; size_t v___x_1662_; lean_object* v___x_1663_; 
v___f_1660_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1660_, 0, v_f_1638_);
v___x_1661_ = lean_usize_of_nat(v___x_1655_);
lean_dec(v___x_1655_);
v___x_1662_ = lean_usize_of_nat(v___x_1656_);
v___x_1663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1636_, v___f_1660_, v_tail_1645_, v___x_1661_, v___x_1662_, v___x_1657_);
return v___x_1663_;
}
}
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1636_, v_t_1637_, v_f_1638_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___boxed(lean_object* v_inst_1665_, lean_object* v_t_1666_, lean_object* v_f_1667_, lean_object* v_start_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_PersistentArray_forM___redArg(v_inst_1665_, v_t_1666_, v_f_1667_, v_start_1668_);
lean_dec(v_start_1668_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM(lean_object* v_00_u03b1_1670_, lean_object* v_m_1671_, lean_object* v_inst_1672_, lean_object* v_t_1673_, lean_object* v_f_1674_, lean_object* v_start_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_PersistentArray_forM___redArg(v_inst_1672_, v_t_1673_, v_f_1674_, v_start_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___boxed(lean_object* v_00_u03b1_1677_, lean_object* v_m_1678_, lean_object* v_inst_1679_, lean_object* v_t_1680_, lean_object* v_f_1681_, lean_object* v_start_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_PersistentArray_forM(v_00_u03b1_1677_, v_m_1678_, v_inst_1679_, v_t_1680_, v_f_1681_, v_start_1682_);
lean_dec(v_start_1682_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___lam__0(lean_object* v_f_1684_, lean_object* v_x1_1685_, lean_object* v_x2_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = lean_apply_2(v_f_1684_, v_x1_1685_, v_x2_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg(lean_object* v_t_1707_, lean_object* v_f_1708_, lean_object* v_init_1709_, lean_object* v_start_1710_){
_start:
{
lean_object* v___f_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___f_1711_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1711_, 0, v_f_1708_);
v___x_1712_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1713_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1712_, v_t_1707_, v___f_1711_, v_init_1709_, v_start_1710_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___boxed(lean_object* v_t_1714_, lean_object* v_f_1715_, lean_object* v_init_1716_, lean_object* v_start_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_PersistentArray_foldl___redArg(v_t_1714_, v_f_1715_, v_init_1716_, v_start_1717_);
lean_dec(v_start_1717_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl(lean_object* v_00_u03b1_1719_, lean_object* v_00_u03b2_1720_, lean_object* v_t_1721_, lean_object* v_f_1722_, lean_object* v_init_1723_, lean_object* v_start_1724_){
_start:
{
lean_object* v___f_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1725_, 0, v_f_1722_);
v___x_1726_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1727_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1726_, v_t_1721_, v___f_1725_, v_init_1723_, v_start_1724_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___boxed(lean_object* v_00_u03b1_1728_, lean_object* v_00_u03b2_1729_, lean_object* v_t_1730_, lean_object* v_f_1731_, lean_object* v_init_1732_, lean_object* v_start_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_PersistentArray_foldl(v_00_u03b1_1728_, v_00_u03b2_1729_, v_t_1730_, v_f_1731_, v_init_1732_, v_start_1733_);
lean_dec(v_start_1733_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr___redArg(lean_object* v_t_1735_, lean_object* v_f_1736_, lean_object* v_init_1737_){
_start:
{
lean_object* v___f_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___f_1738_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1738_, 0, v_f_1736_);
v___x_1739_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1740_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1739_, v_t_1735_, v___f_1738_, v_init_1737_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr(lean_object* v_00_u03b1_1741_, lean_object* v_00_u03b2_1742_, lean_object* v_t_1743_, lean_object* v_f_1744_, lean_object* v_init_1745_){
_start:
{
lean_object* v___f_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___f_1746_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1746_, 0, v_f_1744_);
v___x_1747_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1748_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1747_, v_t_1743_, v___f_1746_, v_init_1745_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg___lam__0(lean_object* v_p_1749_, lean_object* v_x1_1750_, lean_object* v_x2_1751_){
_start:
{
lean_object* v___x_1752_; uint8_t v___x_1753_; 
lean_inc(v_x2_1751_);
v___x_1752_ = lean_apply_1(v_p_1749_, v_x2_1751_);
v___x_1753_ = lean_unbox(v___x_1752_);
if (v___x_1753_ == 0)
{
lean_dec(v_x2_1751_);
return v_x1_1750_;
}
else
{
lean_object* v___x_1754_; 
v___x_1754_ = l_Lean_PersistentArray_push___redArg(v_x1_1750_, v_x2_1751_);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg(lean_object* v_as_1755_, lean_object* v_p_1756_){
_start:
{
lean_object* v___f_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1757_, 0, v_p_1756_);
v___x_1758_ = lean_unsigned_to_nat(32u);
v___x_1759_ = lean_mk_empty_array_with_capacity(v___x_1758_);
lean_dec_ref(v___x_1759_);
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_1762_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1763_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1762_, v_as_1755_, v___f_1757_, v___x_1761_, v___x_1760_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter(lean_object* v_00_u03b1_1764_, lean_object* v_as_1765_, lean_object* v_p_1766_){
_start:
{
lean_object* v___f_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___f_1767_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1767_, 0, v_p_1766_);
v___x_1768_ = lean_unsigned_to_nat(32u);
v___x_1769_ = lean_mk_empty_array_with_capacity(v___x_1768_);
lean_dec_ref(v___x_1769_);
v___x_1770_ = lean_unsigned_to_nat(0u);
v___x_1771_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_1772_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1773_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1772_, v_as_1765_, v___f_1767_, v___x_1771_, v___x_1770_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(lean_object* v_as_1774_, size_t v_i_1775_, size_t v_stop_1776_, lean_object* v_b_1777_){
_start:
{
uint8_t v___x_1778_; 
v___x_1778_ = lean_usize_dec_eq(v_i_1775_, v_stop_1776_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; size_t v___x_1781_; size_t v___x_1782_; 
v___x_1779_ = lean_array_uget_borrowed(v_as_1774_, v_i_1775_);
lean_inc(v___x_1779_);
v___x_1780_ = lean_array_push(v_b_1777_, v___x_1779_);
v___x_1781_ = ((size_t)1ULL);
v___x_1782_ = lean_usize_add(v_i_1775_, v___x_1781_);
v_i_1775_ = v___x_1782_;
v_b_1777_ = v___x_1780_;
goto _start;
}
else
{
return v_b_1777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg___boxed(lean_object* v_as_1784_, lean_object* v_i_1785_, lean_object* v_stop_1786_, lean_object* v_b_1787_){
_start:
{
size_t v_i_boxed_1788_; size_t v_stop_boxed_1789_; lean_object* v_res_1790_; 
v_i_boxed_1788_ = lean_unbox_usize(v_i_1785_);
lean_dec(v_i_1785_);
v_stop_boxed_1789_ = lean_unbox_usize(v_stop_1786_);
lean_dec(v_stop_1786_);
v_res_1790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1784_, v_i_boxed_1788_, v_stop_boxed_1789_, v_b_1787_);
lean_dec_ref(v_as_1784_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(lean_object* v_x_1791_, lean_object* v_x_1792_){
_start:
{
if (lean_obj_tag(v_x_1791_) == 0)
{
lean_object* v_cs_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_cs_1793_ = lean_ctor_get(v_x_1791_, 0);
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = lean_array_get_size(v_cs_1793_);
v___x_1796_ = lean_nat_dec_lt(v___x_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
return v_x_1792_;
}
else
{
size_t v___x_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = ((size_t)0ULL);
v___x_1798_ = lean_usize_of_nat(v___x_1795_);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1793_, v___x_1797_, v___x_1798_, v_x_1792_);
return v___x_1799_;
}
}
else
{
lean_object* v_vs_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v_vs_1800_ = lean_ctor_get(v_x_1791_, 0);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_array_get_size(v_vs_1800_);
v___x_1803_ = lean_nat_dec_lt(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
return v_x_1792_;
}
else
{
size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = lean_usize_of_nat(v___x_1802_);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1800_, v___x_1804_, v___x_1805_, v_x_1792_);
return v___x_1806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(lean_object* v_as_1807_, size_t v_i_1808_, size_t v_stop_1809_, lean_object* v_b_1810_){
_start:
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_usize_dec_eq(v_i_1808_, v_stop_1809_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; size_t v___x_1814_; size_t v___x_1815_; 
v___x_1812_ = lean_array_uget_borrowed(v_as_1807_, v_i_1808_);
v___x_1813_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v___x_1812_, v_b_1810_);
v___x_1814_ = ((size_t)1ULL);
v___x_1815_ = lean_usize_add(v_i_1808_, v___x_1814_);
v_i_1808_ = v___x_1815_;
v_b_1810_ = v___x_1813_;
goto _start;
}
else
{
return v_b_1810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_1817_, lean_object* v_i_1818_, lean_object* v_stop_1819_, lean_object* v_b_1820_){
_start:
{
size_t v_i_boxed_1821_; size_t v_stop_boxed_1822_; lean_object* v_res_1823_; 
v_i_boxed_1821_ = lean_unbox_usize(v_i_1818_);
lean_dec(v_i_1818_);
v_stop_boxed_1822_ = lean_unbox_usize(v_stop_1819_);
lean_dec(v_stop_1819_);
v_res_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1817_, v_i_boxed_1821_, v_stop_boxed_1822_, v_b_1820_);
lean_dec_ref(v_as_1817_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(lean_object* v_x_1824_, lean_object* v_x_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1824_, v_x_1825_);
lean_dec_ref(v_x_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(lean_object* v_x_1827_, size_t v_x_1828_, size_t v_x_1829_, lean_object* v_x_1830_){
_start:
{
if (lean_obj_tag(v_x_1827_) == 0)
{
lean_object* v_cs_1831_; lean_object* v___x_1832_; size_t v___x_1833_; lean_object* v_j_1834_; lean_object* v___x_1835_; size_t v___x_1836_; size_t v___x_1837_; size_t v___x_1838_; size_t v___x_1839_; size_t v___x_1840_; size_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v_cs_1831_ = lean_ctor_get(v_x_1827_, 0);
v___x_1832_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_1833_ = lean_usize_shift_right(v_x_1828_, v_x_1829_);
v_j_1834_ = lean_usize_to_nat(v___x_1833_);
v___x_1835_ = lean_array_get_borrowed(v___x_1832_, v_cs_1831_, v_j_1834_);
v___x_1836_ = ((size_t)1ULL);
v___x_1837_ = lean_usize_shift_left(v___x_1836_, v_x_1829_);
v___x_1838_ = lean_usize_sub(v___x_1837_, v___x_1836_);
v___x_1839_ = lean_usize_land(v_x_1828_, v___x_1838_);
v___x_1840_ = ((size_t)5ULL);
v___x_1841_ = lean_usize_sub(v_x_1829_, v___x_1840_);
v___x_1842_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v___x_1835_, v___x_1839_, v___x_1841_, v_x_1830_);
v___x_1843_ = lean_unsigned_to_nat(1u);
v___x_1844_ = lean_nat_add(v_j_1834_, v___x_1843_);
lean_dec(v_j_1834_);
v___x_1845_ = lean_array_get_size(v_cs_1831_);
v___x_1846_ = lean_nat_dec_lt(v___x_1844_, v___x_1845_);
if (v___x_1846_ == 0)
{
lean_dec(v___x_1844_);
return v___x_1842_;
}
else
{
size_t v___x_1847_; size_t v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_usize_of_nat(v___x_1844_);
lean_dec(v___x_1844_);
v___x_1848_ = lean_usize_of_nat(v___x_1845_);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1831_, v___x_1847_, v___x_1848_, v___x_1842_);
return v___x_1849_;
}
}
else
{
lean_object* v_vs_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v_vs_1850_ = lean_ctor_get(v_x_1827_, 0);
v___x_1851_ = lean_usize_to_nat(v_x_1828_);
v___x_1852_ = lean_array_get_size(v_vs_1850_);
v___x_1853_ = lean_nat_dec_lt(v___x_1851_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_dec(v___x_1851_);
return v_x_1830_;
}
else
{
size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = lean_usize_of_nat(v___x_1851_);
lean_dec(v___x_1851_);
v___x_1855_ = lean_usize_of_nat(v___x_1852_);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1850_, v___x_1854_, v___x_1855_, v_x_1830_);
return v___x_1856_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_x_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_){
_start:
{
size_t v_x_1118__boxed_1861_; size_t v_x_1119__boxed_1862_; lean_object* v_res_1863_; 
v_x_1118__boxed_1861_ = lean_unbox_usize(v_x_1858_);
lean_dec(v_x_1858_);
v_x_1119__boxed_1862_ = lean_unbox_usize(v_x_1859_);
lean_dec(v_x_1859_);
v_res_1863_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1857_, v_x_1118__boxed_1861_, v_x_1119__boxed_1862_, v_x_1860_);
lean_dec_ref(v_x_1857_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(lean_object* v_t_1864_, lean_object* v_init_1865_, lean_object* v_start_1866_){
_start:
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = lean_nat_dec_eq(v_start_1866_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v_root_1869_; lean_object* v_tail_1870_; size_t v_shift_1871_; lean_object* v_tailOff_1872_; uint8_t v___x_1873_; 
v_root_1869_ = lean_ctor_get(v_t_1864_, 0);
v_tail_1870_ = lean_ctor_get(v_t_1864_, 1);
v_shift_1871_ = lean_ctor_get_usize(v_t_1864_, 4);
v_tailOff_1872_ = lean_ctor_get(v_t_1864_, 3);
v___x_1873_ = lean_nat_dec_le(v_tailOff_1872_, v_start_1866_);
if (v___x_1873_ == 0)
{
size_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1874_ = lean_usize_of_nat(v_start_1866_);
v___x_1875_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_root_1869_, v___x_1874_, v_shift_1871_, v_init_1865_);
v___x_1876_ = lean_array_get_size(v_tail_1870_);
v___x_1877_ = lean_nat_dec_lt(v___x_1867_, v___x_1876_);
if (v___x_1877_ == 0)
{
return v___x_1875_;
}
else
{
size_t v___x_1878_; size_t v___x_1879_; lean_object* v___x_1880_; 
v___x_1878_ = ((size_t)0ULL);
v___x_1879_ = lean_usize_of_nat(v___x_1876_);
v___x_1880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1870_, v___x_1878_, v___x_1879_, v___x_1875_);
return v___x_1880_;
}
}
else
{
lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1881_ = lean_nat_sub(v_start_1866_, v_tailOff_1872_);
v___x_1882_ = lean_array_get_size(v_tail_1870_);
v___x_1883_ = lean_nat_dec_lt(v___x_1881_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_dec(v___x_1881_);
return v_init_1865_;
}
else
{
size_t v___x_1884_; size_t v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_usize_of_nat(v___x_1881_);
lean_dec(v___x_1881_);
v___x_1885_ = lean_usize_of_nat(v___x_1882_);
v___x_1886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1870_, v___x_1884_, v___x_1885_, v_init_1865_);
return v___x_1886_;
}
}
}
else
{
lean_object* v_root_1887_; lean_object* v_tail_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v_root_1887_ = lean_ctor_get(v_t_1864_, 0);
v_tail_1888_ = lean_ctor_get(v_t_1864_, 1);
v___x_1889_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_root_1887_, v_init_1865_);
v___x_1890_ = lean_array_get_size(v_tail_1888_);
v___x_1891_ = lean_nat_dec_lt(v___x_1867_, v___x_1890_);
if (v___x_1891_ == 0)
{
return v___x_1889_;
}
else
{
size_t v___x_1892_; size_t v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = ((size_t)0ULL);
v___x_1893_ = lean_usize_of_nat(v___x_1890_);
v___x_1894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1888_, v___x_1892_, v___x_1893_, v___x_1889_);
return v___x_1894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(lean_object* v_t_1895_, lean_object* v_init_1896_, lean_object* v_start_1897_){
_start:
{
lean_object* v_res_1898_; 
v_res_1898_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1895_, v_init_1896_, v_start_1897_);
lean_dec(v_start_1897_);
lean_dec_ref(v_t_1895_);
return v_res_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object* v_t_1899_){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
v___x_1902_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1899_, v___x_1901_, v___x_1900_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg___boxed(lean_object* v_t_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_PersistentArray_toArray___redArg(v_t_1903_);
lean_dec_ref(v_t_1903_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray(lean_object* v_00_u03b1_1905_, lean_object* v_t_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_PersistentArray_toArray___redArg(v_t_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___boxed(lean_object* v_00_u03b1_1908_, lean_object* v_t_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_PersistentArray_toArray(v_00_u03b1_1908_, v_t_1909_);
lean_dec_ref(v_t_1909_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(lean_object* v_00_u03b1_1911_, lean_object* v_t_1912_, lean_object* v_init_1913_, lean_object* v_start_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1912_, v_init_1913_, v_start_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(lean_object* v_00_u03b1_1916_, lean_object* v_t_1917_, lean_object* v_init_1918_, lean_object* v_start_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(v_00_u03b1_1916_, v_t_1917_, v_init_1918_, v_start_1919_);
lean_dec(v_start_1919_);
lean_dec_ref(v_t_1917_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(lean_object* v_00_u03b1_1921_, lean_object* v_x_1922_, size_t v_x_1923_, size_t v_x_1924_, lean_object* v_x_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1922_, v_x_1923_, v_x_1924_, v_x_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1927_, lean_object* v_x_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_, lean_object* v_x_1931_){
_start:
{
size_t v_x_1236__boxed_1932_; size_t v_x_1237__boxed_1933_; lean_object* v_res_1934_; 
v_x_1236__boxed_1932_ = lean_unbox_usize(v_x_1929_);
lean_dec(v_x_1929_);
v_x_1237__boxed_1933_ = lean_unbox_usize(v_x_1930_);
lean_dec(v_x_1930_);
v_res_1934_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(v_00_u03b1_1927_, v_x_1928_, v_x_1236__boxed_1932_, v_x_1237__boxed_1933_, v_x_1931_);
lean_dec_ref(v_x_1928_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(lean_object* v_00_u03b1_1935_, lean_object* v_as_1936_, size_t v_i_1937_, size_t v_stop_1938_, lean_object* v_b_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1936_, v_i_1937_, v_stop_1938_, v_b_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1941_, lean_object* v_as_1942_, lean_object* v_i_1943_, lean_object* v_stop_1944_, lean_object* v_b_1945_){
_start:
{
size_t v_i_boxed_1946_; size_t v_stop_boxed_1947_; lean_object* v_res_1948_; 
v_i_boxed_1946_ = lean_unbox_usize(v_i_1943_);
lean_dec(v_i_1943_);
v_stop_boxed_1947_ = lean_unbox_usize(v_stop_1944_);
lean_dec(v_stop_1944_);
v_res_1948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(v_00_u03b1_1941_, v_as_1942_, v_i_boxed_1946_, v_stop_boxed_1947_, v_b_1945_);
lean_dec_ref(v_as_1942_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(lean_object* v_00_u03b1_1949_, lean_object* v_x_1950_, lean_object* v_x_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1950_, v_x_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1953_, lean_object* v_x_1954_, lean_object* v_x_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(v_00_u03b1_1953_, v_x_1954_, v_x_1955_);
lean_dec_ref(v_x_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1957_, lean_object* v_as_1958_, size_t v_i_1959_, size_t v_stop_1960_, lean_object* v_b_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1958_, v_i_1959_, v_stop_1960_, v_b_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1963_, lean_object* v_as_1964_, lean_object* v_i_1965_, lean_object* v_stop_1966_, lean_object* v_b_1967_){
_start:
{
size_t v_i_boxed_1968_; size_t v_stop_boxed_1969_; lean_object* v_res_1970_; 
v_i_boxed_1968_ = lean_unbox_usize(v_i_1965_);
lean_dec(v_i_1965_);
v_stop_boxed_1969_ = lean_unbox_usize(v_stop_1966_);
lean_dec(v_stop_1966_);
v_res_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(v_00_u03b1_1963_, v_as_1964_, v_i_boxed_1968_, v_stop_boxed_1969_, v_b_1967_);
lean_dec_ref(v_as_1964_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(lean_object* v_as_1971_, size_t v_i_1972_, size_t v_stop_1973_, lean_object* v_b_1974_){
_start:
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_usize_dec_eq(v_i_1972_, v_stop_1973_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; size_t v___x_1978_; size_t v___x_1979_; 
v___x_1976_ = lean_array_uget_borrowed(v_as_1971_, v_i_1972_);
lean_inc(v___x_1976_);
v___x_1977_ = l_Lean_PersistentArray_push___redArg(v_b_1974_, v___x_1976_);
v___x_1978_ = ((size_t)1ULL);
v___x_1979_ = lean_usize_add(v_i_1972_, v___x_1978_);
v_i_1972_ = v___x_1979_;
v_b_1974_ = v___x_1977_;
goto _start;
}
else
{
return v_b_1974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg___boxed(lean_object* v_as_1981_, lean_object* v_i_1982_, lean_object* v_stop_1983_, lean_object* v_b_1984_){
_start:
{
size_t v_i_boxed_1985_; size_t v_stop_boxed_1986_; lean_object* v_res_1987_; 
v_i_boxed_1985_ = lean_unbox_usize(v_i_1982_);
lean_dec(v_i_1982_);
v_stop_boxed_1986_ = lean_unbox_usize(v_stop_1983_);
lean_dec(v_stop_1983_);
v_res_1987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_1981_, v_i_boxed_1985_, v_stop_boxed_1986_, v_b_1984_);
lean_dec_ref(v_as_1981_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(lean_object* v_x_1988_, lean_object* v_x_1989_){
_start:
{
if (lean_obj_tag(v_x_1988_) == 0)
{
lean_object* v_cs_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v_cs_1990_ = lean_ctor_get(v_x_1988_, 0);
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = lean_array_get_size(v_cs_1990_);
v___x_1993_ = lean_nat_dec_lt(v___x_1991_, v___x_1992_);
if (v___x_1993_ == 0)
{
return v_x_1989_;
}
else
{
size_t v___x_1994_; size_t v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = lean_usize_of_nat(v___x_1992_);
v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_1990_, v___x_1994_, v___x_1995_, v_x_1989_);
return v___x_1996_;
}
}
else
{
lean_object* v_vs_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v_vs_1997_ = lean_ctor_get(v_x_1988_, 0);
v___x_1998_ = lean_unsigned_to_nat(0u);
v___x_1999_ = lean_array_get_size(v_vs_1997_);
v___x_2000_ = lean_nat_dec_lt(v___x_1998_, v___x_1999_);
if (v___x_2000_ == 0)
{
return v_x_1989_;
}
else
{
size_t v___x_2001_; size_t v___x_2002_; lean_object* v___x_2003_; 
v___x_2001_ = ((size_t)0ULL);
v___x_2002_ = lean_usize_of_nat(v___x_1999_);
v___x_2003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_1997_, v___x_2001_, v___x_2002_, v_x_1989_);
return v___x_2003_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2004_, size_t v_i_2005_, size_t v_stop_2006_, lean_object* v_b_2007_){
_start:
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_usize_dec_eq(v_i_2005_, v_stop_2006_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; lean_object* v___x_2010_; size_t v___x_2011_; size_t v___x_2012_; 
v___x_2009_ = lean_array_uget_borrowed(v_as_2004_, v_i_2005_);
v___x_2010_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v___x_2009_, v_b_2007_);
v___x_2011_ = ((size_t)1ULL);
v___x_2012_ = lean_usize_add(v_i_2005_, v___x_2011_);
v_i_2005_ = v___x_2012_;
v_b_2007_ = v___x_2010_;
goto _start;
}
else
{
return v_b_2007_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2014_, lean_object* v_i_2015_, lean_object* v_stop_2016_, lean_object* v_b_2017_){
_start:
{
size_t v_i_boxed_2018_; size_t v_stop_boxed_2019_; lean_object* v_res_2020_; 
v_i_boxed_2018_ = lean_unbox_usize(v_i_2015_);
lean_dec(v_i_2015_);
v_stop_boxed_2019_ = lean_unbox_usize(v_stop_2016_);
lean_dec(v_stop_2016_);
v_res_2020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2014_, v_i_boxed_2018_, v_stop_boxed_2019_, v_b_2017_);
lean_dec_ref(v_as_2014_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(lean_object* v_x_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2021_, v_x_2022_);
lean_dec_ref(v_x_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(lean_object* v_x_2024_, size_t v_x_2025_, size_t v_x_2026_, lean_object* v_x_2027_){
_start:
{
if (lean_obj_tag(v_x_2024_) == 0)
{
lean_object* v_cs_2028_; lean_object* v___x_2029_; size_t v___x_2030_; lean_object* v_j_2031_; lean_object* v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; size_t v___x_2037_; size_t v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v_cs_2028_ = lean_ctor_get(v_x_2024_, 0);
v___x_2029_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_2030_ = lean_usize_shift_right(v_x_2025_, v_x_2026_);
v_j_2031_ = lean_usize_to_nat(v___x_2030_);
v___x_2032_ = lean_array_get_borrowed(v___x_2029_, v_cs_2028_, v_j_2031_);
v___x_2033_ = ((size_t)1ULL);
v___x_2034_ = lean_usize_shift_left(v___x_2033_, v_x_2026_);
v___x_2035_ = lean_usize_sub(v___x_2034_, v___x_2033_);
v___x_2036_ = lean_usize_land(v_x_2025_, v___x_2035_);
v___x_2037_ = ((size_t)5ULL);
v___x_2038_ = lean_usize_sub(v_x_2026_, v___x_2037_);
v___x_2039_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v___x_2032_, v___x_2036_, v___x_2038_, v_x_2027_);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_add(v_j_2031_, v___x_2040_);
lean_dec(v_j_2031_);
v___x_2042_ = lean_array_get_size(v_cs_2028_);
v___x_2043_ = lean_nat_dec_lt(v___x_2041_, v___x_2042_);
if (v___x_2043_ == 0)
{
lean_dec(v___x_2041_);
return v___x_2039_;
}
else
{
size_t v___x_2044_; size_t v___x_2045_; lean_object* v___x_2046_; 
v___x_2044_ = lean_usize_of_nat(v___x_2041_);
lean_dec(v___x_2041_);
v___x_2045_ = lean_usize_of_nat(v___x_2042_);
v___x_2046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2028_, v___x_2044_, v___x_2045_, v___x_2039_);
return v___x_2046_;
}
}
else
{
lean_object* v_vs_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v_vs_2047_ = lean_ctor_get(v_x_2024_, 0);
v___x_2048_ = lean_usize_to_nat(v_x_2025_);
v___x_2049_ = lean_array_get_size(v_vs_2047_);
v___x_2050_ = lean_nat_dec_lt(v___x_2048_, v___x_2049_);
if (v___x_2050_ == 0)
{
lean_dec(v___x_2048_);
return v_x_2027_;
}
else
{
size_t v___x_2051_; size_t v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = lean_usize_of_nat(v___x_2048_);
lean_dec(v___x_2048_);
v___x_2052_ = lean_usize_of_nat(v___x_2049_);
v___x_2053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2047_, v___x_2051_, v___x_2052_, v_x_2027_);
return v___x_2053_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(lean_object* v_x_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_x_2057_){
_start:
{
size_t v_x_1125__boxed_2058_; size_t v_x_1126__boxed_2059_; lean_object* v_res_2060_; 
v_x_1125__boxed_2058_ = lean_unbox_usize(v_x_2055_);
lean_dec(v_x_2055_);
v_x_1126__boxed_2059_ = lean_unbox_usize(v_x_2056_);
lean_dec(v_x_2056_);
v_res_2060_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2054_, v_x_1125__boxed_2058_, v_x_1126__boxed_2059_, v_x_2057_);
lean_dec_ref(v_x_2054_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(lean_object* v_t_2061_, lean_object* v_init_2062_, lean_object* v_start_2063_){
_start:
{
lean_object* v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = lean_unsigned_to_nat(0u);
v___x_2065_ = lean_nat_dec_eq(v_start_2063_, v___x_2064_);
if (v___x_2065_ == 0)
{
lean_object* v_root_2066_; lean_object* v_tail_2067_; size_t v_shift_2068_; lean_object* v_tailOff_2069_; uint8_t v___x_2070_; 
v_root_2066_ = lean_ctor_get(v_t_2061_, 0);
v_tail_2067_ = lean_ctor_get(v_t_2061_, 1);
v_shift_2068_ = lean_ctor_get_usize(v_t_2061_, 4);
v_tailOff_2069_ = lean_ctor_get(v_t_2061_, 3);
v___x_2070_ = lean_nat_dec_le(v_tailOff_2069_, v_start_2063_);
if (v___x_2070_ == 0)
{
size_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2071_ = lean_usize_of_nat(v_start_2063_);
v___x_2072_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_root_2066_, v___x_2071_, v_shift_2068_, v_init_2062_);
v___x_2073_ = lean_array_get_size(v_tail_2067_);
v___x_2074_ = lean_nat_dec_lt(v___x_2064_, v___x_2073_);
if (v___x_2074_ == 0)
{
return v___x_2072_;
}
else
{
size_t v___x_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = ((size_t)0ULL);
v___x_2076_ = lean_usize_of_nat(v___x_2073_);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2067_, v___x_2075_, v___x_2076_, v___x_2072_);
return v___x_2077_;
}
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2078_ = lean_nat_sub(v_start_2063_, v_tailOff_2069_);
v___x_2079_ = lean_array_get_size(v_tail_2067_);
v___x_2080_ = lean_nat_dec_lt(v___x_2078_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_dec(v___x_2078_);
return v_init_2062_;
}
else
{
size_t v___x_2081_; size_t v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_usize_of_nat(v___x_2078_);
lean_dec(v___x_2078_);
v___x_2082_ = lean_usize_of_nat(v___x_2079_);
v___x_2083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2067_, v___x_2081_, v___x_2082_, v_init_2062_);
return v___x_2083_;
}
}
}
else
{
lean_object* v_root_2084_; lean_object* v_tail_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; 
v_root_2084_ = lean_ctor_get(v_t_2061_, 0);
v_tail_2085_ = lean_ctor_get(v_t_2061_, 1);
v___x_2086_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_root_2084_, v_init_2062_);
v___x_2087_ = lean_array_get_size(v_tail_2085_);
v___x_2088_ = lean_nat_dec_lt(v___x_2064_, v___x_2087_);
if (v___x_2088_ == 0)
{
return v___x_2086_;
}
else
{
size_t v___x_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = ((size_t)0ULL);
v___x_2090_ = lean_usize_of_nat(v___x_2087_);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2085_, v___x_2089_, v___x_2090_, v___x_2086_);
return v___x_2091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(lean_object* v_t_2092_, lean_object* v_init_2093_, lean_object* v_start_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2092_, v_init_2093_, v_start_2094_);
lean_dec(v_start_2094_);
lean_dec_ref(v_t_2092_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg(lean_object* v_t_u2081_2096_, lean_object* v_t_u2082_2097_){
_start:
{
uint8_t v___x_2098_; 
v___x_2098_ = l_Lean_PersistentArray_isEmpty___redArg(v_t_u2081_2096_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2099_ = lean_unsigned_to_nat(0u);
v___x_2100_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_u2082_2097_, v_t_u2081_2096_, v___x_2099_);
return v___x_2100_;
}
else
{
lean_dec_ref(v_t_u2081_2096_);
lean_inc_ref(v_t_u2082_2097_);
return v_t_u2082_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg___boxed(lean_object* v_t_u2081_2101_, lean_object* v_t_u2082_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2101_, v_t_u2082_2102_);
lean_dec_ref(v_t_u2082_2102_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append(lean_object* v_00_u03b1_2104_, lean_object* v_t_u2081_2105_, lean_object* v_t_u2082_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2105_, v_t_u2082_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___boxed(lean_object* v_00_u03b1_2108_, lean_object* v_t_u2081_2109_, lean_object* v_t_u2082_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_PersistentArray_append(v_00_u03b1_2108_, v_t_u2081_2109_, v_t_u2082_2110_);
lean_dec_ref(v_t_u2082_2110_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(lean_object* v_00_u03b1_2112_, lean_object* v_t_2113_, lean_object* v_init_2114_, lean_object* v_start_2115_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2113_, v_init_2114_, v_start_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(lean_object* v_00_u03b1_2117_, lean_object* v_t_2118_, lean_object* v_init_2119_, lean_object* v_start_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(v_00_u03b1_2117_, v_t_2118_, v_init_2119_, v_start_2120_);
lean_dec(v_start_2120_);
lean_dec_ref(v_t_2118_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(lean_object* v_00_u03b1_2122_, lean_object* v_x_2123_, size_t v_x_2124_, size_t v_x_2125_, lean_object* v_x_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2123_, v_x_2124_, v_x_2125_, v_x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2128_, lean_object* v_x_2129_, lean_object* v_x_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_){
_start:
{
size_t v_x_1241__boxed_2133_; size_t v_x_1242__boxed_2134_; lean_object* v_res_2135_; 
v_x_1241__boxed_2133_ = lean_unbox_usize(v_x_2130_);
lean_dec(v_x_2130_);
v_x_1242__boxed_2134_ = lean_unbox_usize(v_x_2131_);
lean_dec(v_x_2131_);
v_res_2135_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(v_00_u03b1_2128_, v_x_2129_, v_x_1241__boxed_2133_, v_x_1242__boxed_2134_, v_x_2132_);
lean_dec_ref(v_x_2129_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(lean_object* v_00_u03b1_2136_, lean_object* v_as_2137_, size_t v_i_2138_, size_t v_stop_2139_, lean_object* v_b_2140_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2137_, v_i_2138_, v_stop_2139_, v_b_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2142_, lean_object* v_as_2143_, lean_object* v_i_2144_, lean_object* v_stop_2145_, lean_object* v_b_2146_){
_start:
{
size_t v_i_boxed_2147_; size_t v_stop_boxed_2148_; lean_object* v_res_2149_; 
v_i_boxed_2147_ = lean_unbox_usize(v_i_2144_);
lean_dec(v_i_2144_);
v_stop_boxed_2148_ = lean_unbox_usize(v_stop_2145_);
lean_dec(v_stop_2145_);
v_res_2149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(v_00_u03b1_2142_, v_as_2143_, v_i_boxed_2147_, v_stop_boxed_2148_, v_b_2146_);
lean_dec_ref(v_as_2143_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(lean_object* v_00_u03b1_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2151_, v_x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(v_00_u03b1_2154_, v_x_2155_, v_x_2156_);
lean_dec_ref(v_x_2155_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2158_, lean_object* v_as_2159_, size_t v_i_2160_, size_t v_stop_2161_, lean_object* v_b_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2159_, v_i_2160_, v_stop_2161_, v_b_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2164_, lean_object* v_as_2165_, lean_object* v_i_2166_, lean_object* v_stop_2167_, lean_object* v_b_2168_){
_start:
{
size_t v_i_boxed_2169_; size_t v_stop_boxed_2170_; lean_object* v_res_2171_; 
v_i_boxed_2169_ = lean_unbox_usize(v_i_2166_);
lean_dec(v_i_2166_);
v_stop_boxed_2170_ = lean_unbox_usize(v_stop_2167_);
lean_dec(v_stop_2167_);
v_res_2171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(v_00_u03b1_2164_, v_as_2165_, v_i_boxed_2169_, v_stop_boxed_2170_, v_b_2168_);
lean_dec_ref(v_as_2165_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend___redArg(){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___redArg___closed__0));
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend___redArg___boxed(lean_object* v___dummy_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_PersistentArray_instAppend___redArg();
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend(lean_object* v_00_u03b1_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___redArg___closed__0));
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(lean_object* v_f_2179_, lean_object* v_x_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = lean_apply_1(v_f_2179_, v_x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg(lean_object* v_t_2182_, lean_object* v_f_2183_){
_start:
{
lean_object* v___f_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___f_2184_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2184_, 0, v_f_2183_);
v___x_2185_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2186_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2185_, v_t_2182_, v___f_2184_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f(lean_object* v_00_u03b1_2187_, lean_object* v_00_u03b2_2188_, lean_object* v_t_2189_, lean_object* v_f_2190_){
_start:
{
lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___f_2191_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2191_, 0, v_f_2190_);
v___x_2192_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2193_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2192_, v_t_2189_, v___f_2191_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f___redArg(lean_object* v_t_2194_, lean_object* v_f_2195_){
_start:
{
lean_object* v___f_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2196_, 0, v_f_2195_);
v___x_2197_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2198_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2197_, v_t_2194_, v___f_2196_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f(lean_object* v_00_u03b1_2199_, lean_object* v_00_u03b2_2200_, lean_object* v_t_2201_, lean_object* v_f_2202_){
_start:
{
lean_object* v___f_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___f_2203_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2203_, 0, v_f_2202_);
v___x_2204_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2205_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2204_, v_t_2201_, v___f_2203_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(lean_object* v_as_2206_, size_t v_i_2207_, size_t v_stop_2208_, lean_object* v_b_2209_){
_start:
{
uint8_t v___x_2210_; 
v___x_2210_ = lean_usize_dec_eq(v_i_2207_, v_stop_2208_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; 
v___x_2211_ = lean_array_uget_borrowed(v_as_2206_, v_i_2207_);
lean_inc(v___x_2211_);
v___x_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v_b_2209_);
v___x_2213_ = ((size_t)1ULL);
v___x_2214_ = lean_usize_add(v_i_2207_, v___x_2213_);
v_i_2207_ = v___x_2214_;
v_b_2209_ = v___x_2212_;
goto _start;
}
else
{
return v_b_2209_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg___boxed(lean_object* v_as_2216_, lean_object* v_i_2217_, lean_object* v_stop_2218_, lean_object* v_b_2219_){
_start:
{
size_t v_i_boxed_2220_; size_t v_stop_boxed_2221_; lean_object* v_res_2222_; 
v_i_boxed_2220_ = lean_unbox_usize(v_i_2217_);
lean_dec(v_i_2217_);
v_stop_boxed_2221_ = lean_unbox_usize(v_stop_2218_);
lean_dec(v_stop_2218_);
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2216_, v_i_boxed_2220_, v_stop_boxed_2221_, v_b_2219_);
lean_dec_ref(v_as_2216_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(lean_object* v_x_2223_, lean_object* v_x_2224_){
_start:
{
if (lean_obj_tag(v_x_2223_) == 0)
{
lean_object* v_cs_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; uint8_t v___x_2228_; 
v_cs_2225_ = lean_ctor_get(v_x_2223_, 0);
v___x_2226_ = lean_unsigned_to_nat(0u);
v___x_2227_ = lean_array_get_size(v_cs_2225_);
v___x_2228_ = lean_nat_dec_lt(v___x_2226_, v___x_2227_);
if (v___x_2228_ == 0)
{
return v_x_2224_;
}
else
{
size_t v___x_2229_; size_t v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = ((size_t)0ULL);
v___x_2230_ = lean_usize_of_nat(v___x_2227_);
v___x_2231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2225_, v___x_2229_, v___x_2230_, v_x_2224_);
return v___x_2231_;
}
}
else
{
lean_object* v_vs_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v_vs_2232_ = lean_ctor_get(v_x_2223_, 0);
v___x_2233_ = lean_unsigned_to_nat(0u);
v___x_2234_ = lean_array_get_size(v_vs_2232_);
v___x_2235_ = lean_nat_dec_lt(v___x_2233_, v___x_2234_);
if (v___x_2235_ == 0)
{
return v_x_2224_;
}
else
{
size_t v___x_2236_; size_t v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = ((size_t)0ULL);
v___x_2237_ = lean_usize_of_nat(v___x_2234_);
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2232_, v___x_2236_, v___x_2237_, v_x_2224_);
return v___x_2238_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2239_, size_t v_i_2240_, size_t v_stop_2241_, lean_object* v_b_2242_){
_start:
{
uint8_t v___x_2243_; 
v___x_2243_ = lean_usize_dec_eq(v_i_2240_, v_stop_2241_);
if (v___x_2243_ == 0)
{
lean_object* v___x_2244_; lean_object* v___x_2245_; size_t v___x_2246_; size_t v___x_2247_; 
v___x_2244_ = lean_array_uget_borrowed(v_as_2239_, v_i_2240_);
v___x_2245_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v___x_2244_, v_b_2242_);
v___x_2246_ = ((size_t)1ULL);
v___x_2247_ = lean_usize_add(v_i_2240_, v___x_2246_);
v_i_2240_ = v___x_2247_;
v_b_2242_ = v___x_2245_;
goto _start;
}
else
{
return v_b_2242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2249_, lean_object* v_i_2250_, lean_object* v_stop_2251_, lean_object* v_b_2252_){
_start:
{
size_t v_i_boxed_2253_; size_t v_stop_boxed_2254_; lean_object* v_res_2255_; 
v_i_boxed_2253_ = lean_unbox_usize(v_i_2250_);
lean_dec(v_i_2250_);
v_stop_boxed_2254_ = lean_unbox_usize(v_stop_2251_);
lean_dec(v_stop_2251_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2249_, v_i_boxed_2253_, v_stop_boxed_2254_, v_b_2252_);
lean_dec_ref(v_as_2249_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(lean_object* v_x_2256_, lean_object* v_x_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2256_, v_x_2257_);
lean_dec_ref(v_x_2256_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(lean_object* v_x_2259_, size_t v_x_2260_, size_t v_x_2261_, lean_object* v_x_2262_){
_start:
{
if (lean_obj_tag(v_x_2259_) == 0)
{
lean_object* v_cs_2263_; lean_object* v___x_2264_; size_t v___x_2265_; lean_object* v_j_2266_; lean_object* v___x_2267_; size_t v___x_2268_; size_t v___x_2269_; size_t v___x_2270_; size_t v___x_2271_; size_t v___x_2272_; size_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v_cs_2263_ = lean_ctor_get(v_x_2259_, 0);
v___x_2264_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_2265_ = lean_usize_shift_right(v_x_2260_, v_x_2261_);
v_j_2266_ = lean_usize_to_nat(v___x_2265_);
v___x_2267_ = lean_array_get_borrowed(v___x_2264_, v_cs_2263_, v_j_2266_);
v___x_2268_ = ((size_t)1ULL);
v___x_2269_ = lean_usize_shift_left(v___x_2268_, v_x_2261_);
v___x_2270_ = lean_usize_sub(v___x_2269_, v___x_2268_);
v___x_2271_ = lean_usize_land(v_x_2260_, v___x_2270_);
v___x_2272_ = ((size_t)5ULL);
v___x_2273_ = lean_usize_sub(v_x_2261_, v___x_2272_);
v___x_2274_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v___x_2267_, v___x_2271_, v___x_2273_, v_x_2262_);
v___x_2275_ = lean_unsigned_to_nat(1u);
v___x_2276_ = lean_nat_add(v_j_2266_, v___x_2275_);
lean_dec(v_j_2266_);
v___x_2277_ = lean_array_get_size(v_cs_2263_);
v___x_2278_ = lean_nat_dec_lt(v___x_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_dec(v___x_2276_);
return v___x_2274_;
}
else
{
size_t v___x_2279_; size_t v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_usize_of_nat(v___x_2276_);
lean_dec(v___x_2276_);
v___x_2280_ = lean_usize_of_nat(v___x_2277_);
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2263_, v___x_2279_, v___x_2280_, v___x_2274_);
return v___x_2281_;
}
}
else
{
lean_object* v_vs_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v_vs_2282_ = lean_ctor_get(v_x_2259_, 0);
v___x_2283_ = lean_usize_to_nat(v_x_2260_);
v___x_2284_ = lean_array_get_size(v_vs_2282_);
v___x_2285_ = lean_nat_dec_lt(v___x_2283_, v___x_2284_);
if (v___x_2285_ == 0)
{
lean_dec(v___x_2283_);
return v_x_2262_;
}
else
{
size_t v___x_2286_; size_t v___x_2287_; lean_object* v___x_2288_; 
v___x_2286_ = lean_usize_of_nat(v___x_2283_);
lean_dec(v___x_2283_);
v___x_2287_ = lean_usize_of_nat(v___x_2284_);
v___x_2288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2282_, v___x_2286_, v___x_2287_, v_x_2262_);
return v___x_2288_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(lean_object* v_x_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_, lean_object* v_x_2292_){
_start:
{
size_t v_x_1119__boxed_2293_; size_t v_x_1120__boxed_2294_; lean_object* v_res_2295_; 
v_x_1119__boxed_2293_ = lean_unbox_usize(v_x_2290_);
lean_dec(v_x_2290_);
v_x_1120__boxed_2294_ = lean_unbox_usize(v_x_2291_);
lean_dec(v_x_2291_);
v_res_2295_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2289_, v_x_1119__boxed_2293_, v_x_1120__boxed_2294_, v_x_2292_);
lean_dec_ref(v_x_2289_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(lean_object* v_t_2296_, lean_object* v_init_2297_, lean_object* v_start_2298_){
_start:
{
lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2299_ = lean_unsigned_to_nat(0u);
v___x_2300_ = lean_nat_dec_eq(v_start_2298_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v_root_2301_; lean_object* v_tail_2302_; size_t v_shift_2303_; lean_object* v_tailOff_2304_; uint8_t v___x_2305_; 
v_root_2301_ = lean_ctor_get(v_t_2296_, 0);
v_tail_2302_ = lean_ctor_get(v_t_2296_, 1);
v_shift_2303_ = lean_ctor_get_usize(v_t_2296_, 4);
v_tailOff_2304_ = lean_ctor_get(v_t_2296_, 3);
v___x_2305_ = lean_nat_dec_le(v_tailOff_2304_, v_start_2298_);
if (v___x_2305_ == 0)
{
size_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v___x_2306_ = lean_usize_of_nat(v_start_2298_);
v___x_2307_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_root_2301_, v___x_2306_, v_shift_2303_, v_init_2297_);
v___x_2308_ = lean_array_get_size(v_tail_2302_);
v___x_2309_ = lean_nat_dec_lt(v___x_2299_, v___x_2308_);
if (v___x_2309_ == 0)
{
return v___x_2307_;
}
else
{
size_t v___x_2310_; size_t v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = ((size_t)0ULL);
v___x_2311_ = lean_usize_of_nat(v___x_2308_);
v___x_2312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2302_, v___x_2310_, v___x_2311_, v___x_2307_);
return v___x_2312_;
}
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2313_ = lean_nat_sub(v_start_2298_, v_tailOff_2304_);
v___x_2314_ = lean_array_get_size(v_tail_2302_);
v___x_2315_ = lean_nat_dec_lt(v___x_2313_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_dec(v___x_2313_);
return v_init_2297_;
}
else
{
size_t v___x_2316_; size_t v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = lean_usize_of_nat(v___x_2313_);
lean_dec(v___x_2313_);
v___x_2317_ = lean_usize_of_nat(v___x_2314_);
v___x_2318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2302_, v___x_2316_, v___x_2317_, v_init_2297_);
return v___x_2318_;
}
}
}
else
{
lean_object* v_root_2319_; lean_object* v_tail_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_root_2319_ = lean_ctor_get(v_t_2296_, 0);
v_tail_2320_ = lean_ctor_get(v_t_2296_, 1);
v___x_2321_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_root_2319_, v_init_2297_);
v___x_2322_ = lean_array_get_size(v_tail_2320_);
v___x_2323_ = lean_nat_dec_lt(v___x_2299_, v___x_2322_);
if (v___x_2323_ == 0)
{
return v___x_2321_;
}
else
{
size_t v___x_2324_; size_t v___x_2325_; lean_object* v___x_2326_; 
v___x_2324_ = ((size_t)0ULL);
v___x_2325_ = lean_usize_of_nat(v___x_2322_);
v___x_2326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2320_, v___x_2324_, v___x_2325_, v___x_2321_);
return v___x_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(lean_object* v_t_2327_, lean_object* v_init_2328_, lean_object* v_start_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2327_, v_init_2328_, v_start_2329_);
lean_dec(v_start_2329_);
lean_dec_ref(v_t_2327_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg(lean_object* v_t_2331_){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2332_ = lean_box(0);
v___x_2333_ = lean_unsigned_to_nat(0u);
v___x_2334_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2331_, v___x_2332_, v___x_2333_);
v___x_2335_ = l_List_reverse___redArg(v___x_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg___boxed(lean_object* v_t_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_PersistentArray_toList___redArg(v_t_2336_);
lean_dec_ref(v_t_2336_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList(lean_object* v_00_u03b1_2338_, lean_object* v_t_2339_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_PersistentArray_toList___redArg(v_t_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___boxed(lean_object* v_00_u03b1_2341_, lean_object* v_t_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_PersistentArray_toList(v_00_u03b1_2341_, v_t_2342_);
lean_dec_ref(v_t_2342_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(lean_object* v_00_u03b1_2344_, lean_object* v_t_2345_, lean_object* v_init_2346_, lean_object* v_start_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2345_, v_init_2346_, v_start_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(lean_object* v_00_u03b1_2349_, lean_object* v_t_2350_, lean_object* v_init_2351_, lean_object* v_start_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(v_00_u03b1_2349_, v_t_2350_, v_init_2351_, v_start_2352_);
lean_dec(v_start_2352_);
lean_dec_ref(v_t_2350_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(lean_object* v_00_u03b1_2354_, lean_object* v_x_2355_, size_t v_x_2356_, size_t v_x_2357_, lean_object* v_x_2358_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2355_, v_x_2356_, v_x_2357_, v_x_2358_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2360_, lean_object* v_x_2361_, lean_object* v_x_2362_, lean_object* v_x_2363_, lean_object* v_x_2364_){
_start:
{
size_t v_x_1237__boxed_2365_; size_t v_x_1238__boxed_2366_; lean_object* v_res_2367_; 
v_x_1237__boxed_2365_ = lean_unbox_usize(v_x_2362_);
lean_dec(v_x_2362_);
v_x_1238__boxed_2366_ = lean_unbox_usize(v_x_2363_);
lean_dec(v_x_2363_);
v_res_2367_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(v_00_u03b1_2360_, v_x_2361_, v_x_1237__boxed_2365_, v_x_1238__boxed_2366_, v_x_2364_);
lean_dec_ref(v_x_2361_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(lean_object* v_00_u03b1_2368_, lean_object* v_as_2369_, size_t v_i_2370_, size_t v_stop_2371_, lean_object* v_b_2372_){
_start:
{
lean_object* v___x_2373_; 
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2369_, v_i_2370_, v_stop_2371_, v_b_2372_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2374_, lean_object* v_as_2375_, lean_object* v_i_2376_, lean_object* v_stop_2377_, lean_object* v_b_2378_){
_start:
{
size_t v_i_boxed_2379_; size_t v_stop_boxed_2380_; lean_object* v_res_2381_; 
v_i_boxed_2379_ = lean_unbox_usize(v_i_2376_);
lean_dec(v_i_2376_);
v_stop_boxed_2380_ = lean_unbox_usize(v_stop_2377_);
lean_dec(v_stop_2377_);
v_res_2381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(v_00_u03b1_2374_, v_as_2375_, v_i_boxed_2379_, v_stop_boxed_2380_, v_b_2378_);
lean_dec_ref(v_as_2375_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(lean_object* v_00_u03b1_2382_, lean_object* v_x_2383_, lean_object* v_x_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2383_, v_x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2386_, lean_object* v_x_2387_, lean_object* v_x_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(v_00_u03b1_2386_, v_x_2387_, v_x_2388_);
lean_dec_ref(v_x_2387_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2390_, lean_object* v_as_2391_, size_t v_i_2392_, size_t v_stop_2393_, lean_object* v_b_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2391_, v_i_2392_, v_stop_2393_, v_b_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_as_2397_, lean_object* v_i_2398_, lean_object* v_stop_2399_, lean_object* v_b_2400_){
_start:
{
size_t v_i_boxed_2401_; size_t v_stop_boxed_2402_; lean_object* v_res_2403_; 
v_i_boxed_2401_ = lean_unbox_usize(v_i_2398_);
lean_dec(v_i_2398_);
v_stop_boxed_2402_ = lean_unbox_usize(v_stop_2399_);
lean_dec(v_stop_2399_);
v_res_2403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(v_00_u03b1_2396_, v_as_2397_, v_i_boxed_2401_, v_stop_boxed_2402_, v_b_2400_);
lean_dec_ref(v_as_2397_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg(lean_object* v_inst_2404_, lean_object* v_p_2405_, lean_object* v_x_2406_){
_start:
{
if (lean_obj_tag(v_x_2406_) == 0)
{
lean_object* v_toApplicative_2407_; lean_object* v_cs_2408_; lean_object* v_toPure_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v_toApplicative_2407_ = lean_ctor_get(v_inst_2404_, 0);
v_cs_2408_ = lean_ctor_get(v_x_2406_, 0);
lean_inc_ref(v_cs_2408_);
lean_dec_ref_known(v_x_2406_, 1);
v_toPure_2409_ = lean_ctor_get(v_toApplicative_2407_, 1);
v___x_2410_ = lean_unsigned_to_nat(0u);
v___x_2411_ = lean_array_get_size(v_cs_2408_);
v___x_2412_ = lean_nat_dec_lt(v___x_2410_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
lean_inc(v_toPure_2409_);
lean_dec_ref(v_cs_2408_);
lean_dec(v_p_2405_);
lean_dec_ref(v_inst_2404_);
v___x_2413_ = lean_box(v___x_2412_);
v___x_2414_ = lean_apply_2(v_toPure_2409_, lean_box(0), v___x_2413_);
return v___x_2414_;
}
else
{
if (v___x_2412_ == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
lean_inc(v_toPure_2409_);
lean_dec_ref(v_cs_2408_);
lean_dec(v_p_2405_);
lean_dec_ref(v_inst_2404_);
v___x_2415_ = lean_box(v___x_2412_);
v___x_2416_ = lean_apply_2(v_toPure_2409_, lean_box(0), v___x_2415_);
return v___x_2416_;
}
else
{
lean_object* v___f_2417_; size_t v___x_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
lean_inc_ref(v_inst_2404_);
v___f_2417_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2417_, 0, v_inst_2404_);
lean_closure_set(v___f_2417_, 1, v_p_2405_);
v___x_2418_ = ((size_t)0ULL);
v___x_2419_ = lean_usize_of_nat(v___x_2411_);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2404_, v___f_2417_, v_cs_2408_, v___x_2418_, v___x_2419_);
return v___x_2420_;
}
}
}
else
{
lean_object* v_toApplicative_2421_; lean_object* v_vs_2422_; lean_object* v_toPure_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; uint8_t v___x_2426_; 
v_toApplicative_2421_ = lean_ctor_get(v_inst_2404_, 0);
v_vs_2422_ = lean_ctor_get(v_x_2406_, 0);
lean_inc_ref(v_vs_2422_);
lean_dec_ref_known(v_x_2406_, 1);
v_toPure_2423_ = lean_ctor_get(v_toApplicative_2421_, 1);
v___x_2424_ = lean_unsigned_to_nat(0u);
v___x_2425_ = lean_array_get_size(v_vs_2422_);
v___x_2426_ = lean_nat_dec_lt(v___x_2424_, v___x_2425_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_inc(v_toPure_2423_);
lean_dec_ref(v_vs_2422_);
lean_dec(v_p_2405_);
lean_dec_ref(v_inst_2404_);
v___x_2427_ = lean_box(v___x_2426_);
v___x_2428_ = lean_apply_2(v_toPure_2423_, lean_box(0), v___x_2427_);
return v___x_2428_;
}
else
{
if (v___x_2426_ == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2430_; 
lean_inc(v_toPure_2423_);
lean_dec_ref(v_vs_2422_);
lean_dec(v_p_2405_);
lean_dec_ref(v_inst_2404_);
v___x_2429_ = lean_box(v___x_2426_);
v___x_2430_ = lean_apply_2(v_toPure_2423_, lean_box(0), v___x_2429_);
return v___x_2430_;
}
else
{
size_t v___x_2431_; size_t v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = ((size_t)0ULL);
v___x_2432_ = lean_usize_of_nat(v___x_2425_);
v___x_2433_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2404_, v_p_2405_, v_vs_2422_, v___x_2431_, v___x_2432_);
return v___x_2433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg___lam__0(lean_object* v_inst_2434_, lean_object* v_p_2435_, lean_object* v_c_2436_){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2434_, v_p_2435_, v_c_2436_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux(lean_object* v_00_u03b1_2438_, lean_object* v_m_2439_, lean_object* v_inst_2440_, lean_object* v_p_2441_, lean_object* v_x_2442_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2440_, v_p_2441_, v_x_2442_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0(lean_object* v_tail_2444_, lean_object* v_toPure_2445_, lean_object* v_inst_2446_, lean_object* v_p_2447_, uint8_t v_b_2448_){
_start:
{
if (v_b_2448_ == 0)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; 
v___x_2449_ = lean_unsigned_to_nat(0u);
v___x_2450_ = lean_array_get_size(v_tail_2444_);
v___x_2451_ = lean_nat_dec_lt(v___x_2449_, v___x_2450_);
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
lean_dec(v_p_2447_);
lean_dec_ref(v_inst_2446_);
lean_dec_ref(v_tail_2444_);
v___x_2452_ = lean_box(v___x_2451_);
v___x_2453_ = lean_apply_2(v_toPure_2445_, lean_box(0), v___x_2452_);
return v___x_2453_;
}
else
{
if (v___x_2451_ == 0)
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
lean_dec(v_p_2447_);
lean_dec_ref(v_inst_2446_);
lean_dec_ref(v_tail_2444_);
v___x_2454_ = lean_box(v___x_2451_);
v___x_2455_ = lean_apply_2(v_toPure_2445_, lean_box(0), v___x_2454_);
return v___x_2455_;
}
else
{
size_t v___x_2456_; size_t v___x_2457_; lean_object* v___x_2458_; 
lean_dec(v_toPure_2445_);
v___x_2456_ = ((size_t)0ULL);
v___x_2457_ = lean_usize_of_nat(v___x_2450_);
v___x_2458_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2446_, v_p_2447_, v_tail_2444_, v___x_2456_, v___x_2457_);
return v___x_2458_;
}
}
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
lean_dec(v_p_2447_);
lean_dec_ref(v_inst_2446_);
lean_dec_ref(v_tail_2444_);
v___x_2459_ = lean_box(v_b_2448_);
v___x_2460_ = lean_apply_2(v_toPure_2445_, lean_box(0), v___x_2459_);
return v___x_2460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(lean_object* v_tail_2461_, lean_object* v_toPure_2462_, lean_object* v_inst_2463_, lean_object* v_p_2464_, lean_object* v_b_2465_){
_start:
{
uint8_t v_b_boxed_2466_; lean_object* v_res_2467_; 
v_b_boxed_2466_ = lean_unbox(v_b_2465_);
v_res_2467_ = l_Lean_PersistentArray_anyM___redArg___lam__0(v_tail_2461_, v_toPure_2462_, v_inst_2463_, v_p_2464_, v_b_boxed_2466_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object* v_inst_2468_, lean_object* v_t_2469_, lean_object* v_p_2470_){
_start:
{
lean_object* v_toApplicative_2471_; lean_object* v_toBind_2472_; lean_object* v_root_2473_; lean_object* v_tail_2474_; lean_object* v_toPure_2475_; lean_object* v___x_2476_; lean_object* v___f_2477_; lean_object* v___x_2478_; 
v_toApplicative_2471_ = lean_ctor_get(v_inst_2468_, 0);
v_toBind_2472_ = lean_ctor_get(v_inst_2468_, 1);
lean_inc(v_toBind_2472_);
v_root_2473_ = lean_ctor_get(v_t_2469_, 0);
lean_inc_ref(v_root_2473_);
v_tail_2474_ = lean_ctor_get(v_t_2469_, 1);
lean_inc_ref(v_tail_2474_);
lean_dec_ref(v_t_2469_);
v_toPure_2475_ = lean_ctor_get(v_toApplicative_2471_, 1);
lean_inc(v_toPure_2475_);
lean_inc(v_p_2470_);
lean_inc_ref(v_inst_2468_);
v___x_2476_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2468_, v_p_2470_, v_root_2473_);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2477_, 0, v_tail_2474_);
lean_closure_set(v___f_2477_, 1, v_toPure_2475_);
lean_closure_set(v___f_2477_, 2, v_inst_2468_);
lean_closure_set(v___f_2477_, 3, v_p_2470_);
v___x_2478_ = lean_apply_4(v_toBind_2472_, lean_box(0), lean_box(0), v___x_2476_, v___f_2477_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM(lean_object* v_00_u03b1_2479_, lean_object* v_m_2480_, lean_object* v_inst_2481_, lean_object* v_t_2482_, lean_object* v_p_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2481_, v_t_2482_, v_p_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0(lean_object* v_toPure_2485_, uint8_t v_b_2486_){
_start:
{
if (v_b_2486_ == 0)
{
uint8_t v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = 1;
v___x_2488_ = lean_box(v___x_2487_);
v___x_2489_ = lean_apply_2(v_toPure_2485_, lean_box(0), v___x_2488_);
return v___x_2489_;
}
else
{
uint8_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2490_ = 0;
v___x_2491_ = lean_box(v___x_2490_);
v___x_2492_ = lean_apply_2(v_toPure_2485_, lean_box(0), v___x_2491_);
return v___x_2492_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0___boxed(lean_object* v_toPure_2493_, lean_object* v_b_2494_){
_start:
{
uint8_t v_b_boxed_2495_; lean_object* v_res_2496_; 
v_b_boxed_2495_ = lean_unbox(v_b_2494_);
v_res_2496_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_2493_, v_b_boxed_2495_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__1(lean_object* v_p_2497_, lean_object* v_toBind_2498_, lean_object* v___f_2499_, lean_object* v_v_2500_){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2501_ = lean_apply_1(v_p_2497_, v_v_2500_);
v___x_2502_ = lean_apply_4(v_toBind_2498_, lean_box(0), lean_box(0), v___x_2501_, v___f_2499_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg(lean_object* v_inst_2503_, lean_object* v_a_2504_, lean_object* v_p_2505_){
_start:
{
lean_object* v_toApplicative_2506_; lean_object* v_toBind_2507_; lean_object* v_toPure_2508_; lean_object* v___f_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v_toApplicative_2506_ = lean_ctor_get(v_inst_2503_, 0);
v_toBind_2507_ = lean_ctor_get(v_inst_2503_, 1);
lean_inc_n(v_toBind_2507_, 2);
v_toPure_2508_ = lean_ctor_get(v_toApplicative_2506_, 1);
lean_inc(v_toPure_2508_);
v___f_2509_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2509_, 0, v_toPure_2508_);
lean_inc_ref(v___f_2509_);
v___f_2510_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2510_, 0, v_p_2505_);
lean_closure_set(v___f_2510_, 1, v_toBind_2507_);
lean_closure_set(v___f_2510_, 2, v___f_2509_);
v___x_2511_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2503_, v_a_2504_, v___f_2510_);
v___x_2512_ = lean_apply_4(v_toBind_2507_, lean_box(0), lean_box(0), v___x_2511_, v___f_2509_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM(lean_object* v_00_u03b1_2513_, lean_object* v_m_2514_, lean_object* v_inst_2515_, lean_object* v_a_2516_, lean_object* v_p_2517_){
_start:
{
lean_object* v_toApplicative_2518_; lean_object* v_toBind_2519_; lean_object* v_toPure_2520_; lean_object* v___f_2521_; lean_object* v___f_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v_toApplicative_2518_ = lean_ctor_get(v_inst_2515_, 0);
v_toBind_2519_ = lean_ctor_get(v_inst_2515_, 1);
lean_inc_n(v_toBind_2519_, 2);
v_toPure_2520_ = lean_ctor_get(v_toApplicative_2518_, 1);
lean_inc(v_toPure_2520_);
v___f_2521_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2521_, 0, v_toPure_2520_);
lean_inc_ref(v___f_2521_);
v___f_2522_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2522_, 0, v_p_2517_);
lean_closure_set(v___f_2522_, 1, v_toBind_2519_);
lean_closure_set(v___f_2522_, 2, v___f_2521_);
v___x_2523_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2515_, v_a_2516_, v___f_2522_);
v___x_2524_ = lean_apply_4(v_toBind_2519_, lean_box(0), lean_box(0), v___x_2523_, v___f_2521_);
return v___x_2524_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg___lam__0(lean_object* v_p_2525_, lean_object* v_x_2526_){
_start:
{
lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2527_ = lean_apply_1(v_p_2525_, v_x_2526_);
v___x_2528_ = lean_unbox(v___x_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___lam__0___boxed(lean_object* v_p_2529_, lean_object* v_x_2530_){
_start:
{
uint8_t v_res_2531_; lean_object* v_r_2532_; 
v_res_2531_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_2529_, v_x_2530_);
v_r_2532_ = lean_box(v_res_2531_);
return v_r_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg(lean_object* v_a_2533_, lean_object* v_p_2534_){
_start:
{
lean_object* v___f_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___f_2535_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2535_, 0, v_p_2534_);
v___x_2536_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2537_ = l_Lean_PersistentArray_anyM___redArg(v___x_2536_, v_a_2533_, v___f_2535_);
return v___x_2537_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any(lean_object* v_00_u03b1_2538_, lean_object* v_a_2539_, lean_object* v_p_2540_){
_start:
{
lean_object* v___f_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___f_2541_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2541_, 0, v_p_2540_);
v___x_2542_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2543_ = l_Lean_PersistentArray_anyM___redArg(v___x_2542_, v_a_2539_, v___f_2541_);
v___x_2544_ = lean_unbox(v___x_2543_);
lean_dec(v___x_2543_);
return v___x_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___boxed(lean_object* v_00_u03b1_2545_, lean_object* v_a_2546_, lean_object* v_p_2547_){
_start:
{
uint8_t v_res_2548_; lean_object* v_r_2549_; 
v_res_2548_ = l_Lean_PersistentArray_any(v_00_u03b1_2545_, v_a_2546_, v_p_2547_);
v_r_2549_ = lean_box(v_res_2548_);
return v_r_2549_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg___lam__0(lean_object* v_p_2550_, lean_object* v_x_2551_){
_start:
{
lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2552_ = lean_apply_1(v_p_2550_, v_x_2551_);
v___x_2553_ = lean_unbox(v___x_2552_);
if (v___x_2553_ == 0)
{
uint8_t v___x_2554_; 
v___x_2554_ = 1;
return v___x_2554_;
}
else
{
uint8_t v___x_2555_; 
v___x_2555_ = 0;
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___lam__0___boxed(lean_object* v_p_2556_, lean_object* v_x_2557_){
_start:
{
uint8_t v_res_2558_; lean_object* v_r_2559_; 
v_res_2558_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_2556_, v_x_2557_);
v_r_2559_ = lean_box(v_res_2558_);
return v_r_2559_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg(lean_object* v_a_2560_, lean_object* v_p_2561_){
_start:
{
lean_object* v___f_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___f_2562_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2562_, 0, v_p_2561_);
v___x_2563_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2564_ = l_Lean_PersistentArray_anyM___redArg(v___x_2563_, v_a_2560_, v___f_2562_);
v___x_2565_ = lean_unbox(v___x_2564_);
lean_dec(v___x_2564_);
if (v___x_2565_ == 0)
{
uint8_t v___x_2566_; 
v___x_2566_ = 1;
return v___x_2566_;
}
else
{
uint8_t v___x_2567_; 
v___x_2567_ = 0;
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___boxed(lean_object* v_a_2568_, lean_object* v_p_2569_){
_start:
{
uint8_t v_res_2570_; lean_object* v_r_2571_; 
v_res_2570_ = l_Lean_PersistentArray_all___redArg(v_a_2568_, v_p_2569_);
v_r_2571_ = lean_box(v_res_2570_);
return v_r_2571_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all(lean_object* v_00_u03b1_2572_, lean_object* v_a_2573_, lean_object* v_p_2574_){
_start:
{
lean_object* v___f_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___f_2575_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2575_, 0, v_p_2574_);
v___x_2576_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2577_ = l_Lean_PersistentArray_anyM___redArg(v___x_2576_, v_a_2573_, v___f_2575_);
v___x_2578_ = lean_unbox(v___x_2577_);
lean_dec(v___x_2577_);
if (v___x_2578_ == 0)
{
uint8_t v___x_2579_; 
v___x_2579_ = 1;
return v___x_2579_;
}
else
{
uint8_t v___x_2580_; 
v___x_2580_ = 0;
return v___x_2580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___boxed(lean_object* v_00_u03b1_2581_, lean_object* v_a_2582_, lean_object* v_p_2583_){
_start:
{
uint8_t v_res_2584_; lean_object* v_r_2585_; 
v_res_2584_ = l_Lean_PersistentArray_all(v_00_u03b1_2581_, v_a_2582_, v_p_2583_);
v_r_2585_ = lean_box(v_res_2584_);
return v_r_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__0(lean_object* v_cs_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_cs_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__2(lean_object* v_vs_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2589_, 0, v_vs_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg(lean_object* v_inst_2592_, lean_object* v_f_2593_, lean_object* v_x_2594_){
_start:
{
if (lean_obj_tag(v_x_2594_) == 0)
{
lean_object* v_toApplicative_2595_; lean_object* v_toFunctor_2596_; lean_object* v_cs_2597_; lean_object* v_map_2598_; lean_object* v___f_2599_; lean_object* v___f_2600_; size_t v_sz_2601_; size_t v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v_toApplicative_2595_ = lean_ctor_get(v_inst_2592_, 0);
v_toFunctor_2596_ = lean_ctor_get(v_toApplicative_2595_, 0);
v_cs_2597_ = lean_ctor_get(v_x_2594_, 0);
lean_inc_ref(v_cs_2597_);
lean_dec_ref_known(v_x_2594_, 1);
v_map_2598_ = lean_ctor_get(v_toFunctor_2596_, 0);
lean_inc(v_map_2598_);
v___f_2599_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__0));
lean_inc_ref(v_inst_2592_);
v___f_2600_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapMAux___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2600_, 0, v_inst_2592_);
lean_closure_set(v___f_2600_, 1, v_f_2593_);
v_sz_2601_ = lean_array_size(v_cs_2597_);
v___x_2602_ = ((size_t)0ULL);
v___x_2603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2592_, v___f_2600_, v_sz_2601_, v___x_2602_, v_cs_2597_);
v___x_2604_ = lean_apply_4(v_map_2598_, lean_box(0), lean_box(0), v___f_2599_, v___x_2603_);
return v___x_2604_;
}
else
{
lean_object* v_toApplicative_2605_; lean_object* v_toFunctor_2606_; lean_object* v_vs_2607_; lean_object* v_map_2608_; lean_object* v___f_2609_; size_t v_sz_2610_; size_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v_toApplicative_2605_ = lean_ctor_get(v_inst_2592_, 0);
v_toFunctor_2606_ = lean_ctor_get(v_toApplicative_2605_, 0);
v_vs_2607_ = lean_ctor_get(v_x_2594_, 0);
lean_inc_ref(v_vs_2607_);
lean_dec_ref_known(v_x_2594_, 1);
v_map_2608_ = lean_ctor_get(v_toFunctor_2606_, 0);
lean_inc(v_map_2608_);
v___f_2609_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__1));
v_sz_2610_ = lean_array_size(v_vs_2607_);
v___x_2611_ = ((size_t)0ULL);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2592_, v_f_2593_, v_sz_2610_, v___x_2611_, v_vs_2607_);
v___x_2613_ = lean_apply_4(v_map_2608_, lean_box(0), lean_box(0), v___f_2609_, v___x_2612_);
return v___x_2613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__1(lean_object* v_inst_2614_, lean_object* v_f_2615_, lean_object* v_c_2616_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2614_, v_f_2615_, v_c_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux(lean_object* v_00_u03b1_2618_, lean_object* v_m_2619_, lean_object* v_inst_2620_, lean_object* v_00_u03b2_2621_, lean_object* v_f_2622_, lean_object* v_x_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2620_, v_f_2622_, v_x_2623_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0(lean_object* v_root_2625_, lean_object* v_size_2626_, size_t v_shift_2627_, lean_object* v_tailOff_2628_, lean_object* v_toPure_2629_, lean_object* v_tail_2630_){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2631_, 0, v_root_2625_);
lean_ctor_set(v___x_2631_, 1, v_tail_2630_);
lean_ctor_set(v___x_2631_, 2, v_size_2626_);
lean_ctor_set(v___x_2631_, 3, v_tailOff_2628_);
lean_ctor_set_usize(v___x_2631_, 4, v_shift_2627_);
v___x_2632_ = lean_apply_2(v_toPure_2629_, lean_box(0), v___x_2631_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(lean_object* v_root_2633_, lean_object* v_size_2634_, lean_object* v_shift_2635_, lean_object* v_tailOff_2636_, lean_object* v_toPure_2637_, lean_object* v_tail_2638_){
_start:
{
size_t v_shift_boxed_2639_; lean_object* v_res_2640_; 
v_shift_boxed_2639_ = lean_unbox_usize(v_shift_2635_);
lean_dec(v_shift_2635_);
v_res_2640_ = l_Lean_PersistentArray_mapM___redArg___lam__0(v_root_2633_, v_size_2634_, v_shift_boxed_2639_, v_tailOff_2636_, v_toPure_2637_, v_tail_2638_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1(lean_object* v_size_2641_, size_t v_shift_2642_, lean_object* v_tailOff_2643_, lean_object* v_toPure_2644_, lean_object* v_tail_2645_, lean_object* v_inst_2646_, lean_object* v_f_2647_, lean_object* v_toBind_2648_, lean_object* v_root_2649_){
_start:
{
lean_object* v___x_2650_; lean_object* v___f_2651_; size_t v_sz_2652_; size_t v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2650_ = lean_box_usize(v_shift_2642_);
v___f_2651_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2651_, 0, v_root_2649_);
lean_closure_set(v___f_2651_, 1, v_size_2641_);
lean_closure_set(v___f_2651_, 2, v___x_2650_);
lean_closure_set(v___f_2651_, 3, v_tailOff_2643_);
lean_closure_set(v___f_2651_, 4, v_toPure_2644_);
v_sz_2652_ = lean_array_size(v_tail_2645_);
v___x_2653_ = ((size_t)0ULL);
v___x_2654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2646_, v_f_2647_, v_sz_2652_, v___x_2653_, v_tail_2645_);
v___x_2655_ = lean_apply_4(v_toBind_2648_, lean_box(0), lean_box(0), v___x_2654_, v___f_2651_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(lean_object* v_size_2656_, lean_object* v_shift_2657_, lean_object* v_tailOff_2658_, lean_object* v_toPure_2659_, lean_object* v_tail_2660_, lean_object* v_inst_2661_, lean_object* v_f_2662_, lean_object* v_toBind_2663_, lean_object* v_root_2664_){
_start:
{
size_t v_shift_boxed_2665_; lean_object* v_res_2666_; 
v_shift_boxed_2665_ = lean_unbox_usize(v_shift_2657_);
lean_dec(v_shift_2657_);
v_res_2666_ = l_Lean_PersistentArray_mapM___redArg___lam__1(v_size_2656_, v_shift_boxed_2665_, v_tailOff_2658_, v_toPure_2659_, v_tail_2660_, v_inst_2661_, v_f_2662_, v_toBind_2663_, v_root_2664_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object* v_inst_2667_, lean_object* v_f_2668_, lean_object* v_t_2669_){
_start:
{
lean_object* v_toApplicative_2670_; lean_object* v_toBind_2671_; lean_object* v_root_2672_; lean_object* v_tail_2673_; lean_object* v_size_2674_; size_t v_shift_2675_; lean_object* v_tailOff_2676_; lean_object* v_toPure_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___f_2680_; lean_object* v___x_2681_; 
v_toApplicative_2670_ = lean_ctor_get(v_inst_2667_, 0);
v_toBind_2671_ = lean_ctor_get(v_inst_2667_, 1);
lean_inc_n(v_toBind_2671_, 2);
v_root_2672_ = lean_ctor_get(v_t_2669_, 0);
lean_inc_ref(v_root_2672_);
v_tail_2673_ = lean_ctor_get(v_t_2669_, 1);
lean_inc_ref(v_tail_2673_);
v_size_2674_ = lean_ctor_get(v_t_2669_, 2);
lean_inc(v_size_2674_);
v_shift_2675_ = lean_ctor_get_usize(v_t_2669_, 4);
v_tailOff_2676_ = lean_ctor_get(v_t_2669_, 3);
lean_inc(v_tailOff_2676_);
lean_dec_ref(v_t_2669_);
v_toPure_2677_ = lean_ctor_get(v_toApplicative_2670_, 1);
lean_inc(v_toPure_2677_);
lean_inc(v_f_2668_);
lean_inc_ref(v_inst_2667_);
v___x_2678_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2667_, v_f_2668_, v_root_2672_);
v___x_2679_ = lean_box_usize(v_shift_2675_);
v___f_2680_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2680_, 0, v_size_2674_);
lean_closure_set(v___f_2680_, 1, v___x_2679_);
lean_closure_set(v___f_2680_, 2, v_tailOff_2676_);
lean_closure_set(v___f_2680_, 3, v_toPure_2677_);
lean_closure_set(v___f_2680_, 4, v_tail_2673_);
lean_closure_set(v___f_2680_, 5, v_inst_2667_);
lean_closure_set(v___f_2680_, 6, v_f_2668_);
lean_closure_set(v___f_2680_, 7, v_toBind_2671_);
v___x_2681_ = lean_apply_4(v_toBind_2671_, lean_box(0), lean_box(0), v___x_2678_, v___f_2680_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM(lean_object* v_00_u03b1_2682_, lean_object* v_m_2683_, lean_object* v_inst_2684_, lean_object* v_00_u03b2_2685_, lean_object* v_f_2686_, lean_object* v_t_2687_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_PersistentArray_mapM___redArg(v_inst_2684_, v_f_2686_, v_t_2687_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg___lam__0(lean_object* v_f_2689_, lean_object* v_x_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = lean_apply_1(v_f_2689_, v_x_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg(lean_object* v_f_2692_, lean_object* v_t_2693_){
_start:
{
lean_object* v___f_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___f_2694_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2694_, 0, v_f_2692_);
v___x_2695_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2696_ = l_Lean_PersistentArray_mapM___redArg(v___x_2695_, v___f_2694_, v_t_2693_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map(lean_object* v_00_u03b1_2697_, lean_object* v_00_u03b2_2698_, lean_object* v_f_2699_, lean_object* v_t_2700_){
_start:
{
lean_object* v___f_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___f_2701_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2701_, 0, v_f_2699_);
v___x_2702_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2703_ = l_Lean_PersistentArray_mapM___redArg(v___x_2702_, v___f_2701_, v_t_2700_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg(lean_object* v_x_2704_, lean_object* v_x_2705_, lean_object* v_x_2706_){
_start:
{
if (lean_obj_tag(v_x_2704_) == 0)
{
lean_object* v_cs_2707_; lean_object* v_numNodes_2708_; lean_object* v_depth_2709_; lean_object* v_tailSize_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2728_; 
v_cs_2707_ = lean_ctor_get(v_x_2704_, 0);
v_numNodes_2708_ = lean_ctor_get(v_x_2705_, 0);
v_depth_2709_ = lean_ctor_get(v_x_2705_, 1);
v_tailSize_2710_ = lean_ctor_get(v_x_2705_, 2);
v_isSharedCheck_2728_ = !lean_is_exclusive(v_x_2705_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2712_ = v_x_2705_;
v_isShared_2713_ = v_isSharedCheck_2728_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_tailSize_2710_);
lean_inc(v_depth_2709_);
lean_inc(v_numNodes_2708_);
lean_dec(v_x_2705_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2728_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___y_2717_; uint8_t v___x_2727_; 
v___x_2714_ = lean_unsigned_to_nat(1u);
v___x_2715_ = lean_nat_add(v_numNodes_2708_, v___x_2714_);
lean_dec(v_numNodes_2708_);
v___x_2727_ = lean_nat_dec_le(v_x_2706_, v_depth_2709_);
if (v___x_2727_ == 0)
{
lean_dec(v_depth_2709_);
lean_inc(v_x_2706_);
v___y_2717_ = v_x_2706_;
goto v___jp_2716_;
}
else
{
v___y_2717_ = v_depth_2709_;
goto v___jp_2716_;
}
v___jp_2716_:
{
lean_object* v___x_2719_; 
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 1, v___y_2717_);
lean_ctor_set(v___x_2712_, 0, v___x_2715_);
v___x_2719_ = v___x_2712_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v___y_2717_);
lean_ctor_set(v_reuseFailAlloc_2726_, 2, v_tailSize_2710_);
v___x_2719_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = lean_array_get_size(v_cs_2707_);
v___x_2722_ = lean_nat_dec_lt(v___x_2720_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_dec(v_x_2706_);
return v___x_2719_;
}
else
{
size_t v___x_2723_; size_t v___x_2724_; lean_object* v___x_2725_; 
v___x_2723_ = ((size_t)0ULL);
v___x_2724_ = lean_usize_of_nat(v___x_2721_);
v___x_2725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2706_, v_cs_2707_, v___x_2723_, v___x_2724_, v___x_2719_);
lean_dec(v_x_2706_);
return v___x_2725_;
}
}
}
}
}
else
{
lean_object* v_numNodes_2729_; lean_object* v_depth_2730_; lean_object* v_tailSize_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2744_; 
v_numNodes_2729_ = lean_ctor_get(v_x_2705_, 0);
v_depth_2730_ = lean_ctor_get(v_x_2705_, 1);
v_tailSize_2731_ = lean_ctor_get(v_x_2705_, 2);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_x_2705_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2733_ = v_x_2705_;
v_isShared_2734_ = v_isSharedCheck_2744_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_tailSize_2731_);
lean_inc(v_depth_2730_);
lean_inc(v_numNodes_2729_);
lean_dec(v_x_2705_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2744_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2735_ = lean_unsigned_to_nat(1u);
v___x_2736_ = lean_nat_add(v_numNodes_2729_, v___x_2735_);
lean_dec(v_numNodes_2729_);
v___x_2737_ = lean_nat_dec_le(v_x_2706_, v_depth_2730_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2739_; 
lean_dec(v_depth_2730_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v_x_2706_);
lean_ctor_set(v___x_2733_, 0, v___x_2736_);
v___x_2739_ = v___x_2733_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_x_2706_);
lean_ctor_set(v_reuseFailAlloc_2740_, 2, v_tailSize_2731_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
else
{
lean_object* v___x_2742_; 
lean_dec(v_x_2706_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v___x_2736_);
v___x_2742_ = v___x_2733_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2736_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_depth_2730_);
lean_ctor_set(v_reuseFailAlloc_2743_, 2, v_tailSize_2731_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(lean_object* v_x_2745_, lean_object* v_as_2746_, size_t v_i_2747_, size_t v_stop_2748_, lean_object* v_b_2749_){
_start:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_usize_dec_eq(v_i_2747_, v_stop_2748_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; size_t v___x_2755_; size_t v___x_2756_; 
v___x_2751_ = lean_array_uget_borrowed(v_as_2746_, v_i_2747_);
v___x_2752_ = lean_unsigned_to_nat(1u);
v___x_2753_ = lean_nat_add(v_x_2745_, v___x_2752_);
v___x_2754_ = l_Lean_PersistentArray_collectStats___redArg(v___x_2751_, v_b_2749_, v___x_2753_);
v___x_2755_ = ((size_t)1ULL);
v___x_2756_ = lean_usize_add(v_i_2747_, v___x_2755_);
v_i_2747_ = v___x_2756_;
v_b_2749_ = v___x_2754_;
goto _start;
}
else
{
return v_b_2749_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg___boxed(lean_object* v_x_2758_, lean_object* v_as_2759_, lean_object* v_i_2760_, lean_object* v_stop_2761_, lean_object* v_b_2762_){
_start:
{
size_t v_i_boxed_2763_; size_t v_stop_boxed_2764_; lean_object* v_res_2765_; 
v_i_boxed_2763_ = lean_unbox_usize(v_i_2760_);
lean_dec(v_i_2760_);
v_stop_boxed_2764_ = lean_unbox_usize(v_stop_2761_);
lean_dec(v_stop_2761_);
v_res_2765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2758_, v_as_2759_, v_i_boxed_2763_, v_stop_boxed_2764_, v_b_2762_);
lean_dec_ref(v_as_2759_);
lean_dec(v_x_2758_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg___boxed(lean_object* v_x_2766_, lean_object* v_x_2767_, lean_object* v_x_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2766_, v_x_2767_, v_x_2768_);
lean_dec_ref(v_x_2766_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats(lean_object* v_00_u03b1_2770_, lean_object* v_x_2771_, lean_object* v_x_2772_, lean_object* v_x_2773_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2771_, v_x_2772_, v_x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___boxed(lean_object* v_00_u03b1_2775_, lean_object* v_x_2776_, lean_object* v_x_2777_, lean_object* v_x_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_PersistentArray_collectStats(v_00_u03b1_2775_, v_x_2776_, v_x_2777_, v_x_2778_);
lean_dec_ref(v_x_2776_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(lean_object* v_00_u03b1_2780_, lean_object* v_x_2781_, lean_object* v_as_2782_, size_t v_i_2783_, size_t v_stop_2784_, lean_object* v_b_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2781_, v_as_2782_, v_i_2783_, v_stop_2784_, v_b_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2787_, lean_object* v_x_2788_, lean_object* v_as_2789_, lean_object* v_i_2790_, lean_object* v_stop_2791_, lean_object* v_b_2792_){
_start:
{
size_t v_i_boxed_2793_; size_t v_stop_boxed_2794_; lean_object* v_res_2795_; 
v_i_boxed_2793_ = lean_unbox_usize(v_i_2790_);
lean_dec(v_i_2790_);
v_stop_boxed_2794_ = lean_unbox_usize(v_stop_2791_);
lean_dec(v_stop_2791_);
v_res_2795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(v_00_u03b1_2787_, v_x_2788_, v_as_2789_, v_i_boxed_2793_, v_stop_boxed_2794_, v_b_2792_);
lean_dec_ref(v_as_2789_);
lean_dec(v_x_2788_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg(lean_object* v_r_2796_){
_start:
{
lean_object* v_root_2797_; lean_object* v_tail_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v_root_2797_ = lean_ctor_get(v_r_2796_, 0);
v_tail_2798_ = lean_ctor_get(v_r_2796_, 1);
v___x_2799_ = lean_unsigned_to_nat(0u);
v___x_2800_ = lean_array_get_size(v_tail_2798_);
v___x_2801_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2799_);
lean_ctor_set(v___x_2801_, 1, v___x_2799_);
lean_ctor_set(v___x_2801_, 2, v___x_2800_);
v___x_2802_ = l_Lean_PersistentArray_collectStats___redArg(v_root_2797_, v___x_2801_, v___x_2799_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg___boxed(lean_object* v_r_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_PersistentArray_stats___redArg(v_r_2803_);
lean_dec_ref(v_r_2803_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats(lean_object* v_00_u03b1_2805_, lean_object* v_r_2806_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Lean_PersistentArray_stats___redArg(v_r_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___boxed(lean_object* v_00_u03b1_2808_, lean_object* v_r_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_PersistentArray_stats(v_00_u03b1_2808_, v_r_2809_);
lean_dec_ref(v_r_2809_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Stats_toString(lean_object* v_s_2815_){
_start:
{
lean_object* v_numNodes_2816_; lean_object* v_depth_2817_; lean_object* v_tailSize_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; 
v_numNodes_2816_ = lean_ctor_get(v_s_2815_, 0);
lean_inc(v_numNodes_2816_);
v_depth_2817_ = lean_ctor_get(v_s_2815_, 1);
lean_inc(v_depth_2817_);
v_tailSize_2818_ = lean_ctor_get(v_s_2815_, 2);
lean_inc(v_tailSize_2818_);
lean_dec_ref(v_s_2815_);
v___x_2819_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__0));
v___x_2820_ = l_Nat_reprFast(v_numNodes_2816_);
v___x_2821_ = lean_string_append(v___x_2819_, v___x_2820_);
lean_dec_ref(v___x_2820_);
v___x_2822_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__1));
v___x_2823_ = lean_string_append(v___x_2821_, v___x_2822_);
v___x_2824_ = l_Nat_reprFast(v_depth_2817_);
v___x_2825_ = lean_string_append(v___x_2823_, v___x_2824_);
lean_dec_ref(v___x_2824_);
v___x_2826_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__2));
v___x_2827_ = lean_string_append(v___x_2825_, v___x_2826_);
v___x_2828_ = l_Nat_reprFast(v_tailSize_2818_);
v___x_2829_ = lean_string_append(v___x_2827_, v___x_2828_);
lean_dec_ref(v___x_2828_);
v___x_2830_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__3));
v___x_2831_ = lean_string_append(v___x_2829_, v___x_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(lean_object* v_v_2834_, lean_object* v_j_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v_zero_2837_; uint8_t v_isZero_2838_; 
v_zero_2837_ = lean_unsigned_to_nat(0u);
v_isZero_2838_ = lean_nat_dec_eq(v_j_2835_, v_zero_2837_);
if (v_isZero_2838_ == 1)
{
lean_dec(v_j_2835_);
lean_dec(v_v_2834_);
return v_a_2836_;
}
else
{
lean_object* v_one_2839_; lean_object* v_n_2840_; lean_object* v___x_2841_; 
v_one_2839_ = lean_unsigned_to_nat(1u);
v_n_2840_ = lean_nat_sub(v_j_2835_, v_one_2839_);
lean_dec(v_j_2835_);
lean_inc(v_v_2834_);
v___x_2841_ = l_Lean_PersistentArray_push___redArg(v_a_2836_, v_v_2834_);
v_j_2835_ = v_n_2840_;
v_a_2836_ = v___x_2841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray___redArg(lean_object* v_n_2843_, lean_object* v_v_2844_){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
v___x_2846_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2844_, v_n_2843_, v___x_2845_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray(lean_object* v_00_u03b1_2847_, lean_object* v_n_2848_, lean_object* v_v_2849_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_mkPersistentArray___redArg(v_n_2848_, v_v_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(lean_object* v_00_u03b1_2851_, lean_object* v_v_2852_, lean_object* v_n_2853_, lean_object* v_j_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2852_, v_j_2854_, v_a_2856_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(lean_object* v_00_u03b1_2858_, lean_object* v_v_2859_, lean_object* v_n_2860_, lean_object* v_j_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(v_00_u03b1_2858_, v_v_2859_, v_n_2860_, v_j_2861_, v_a_2862_, v_a_2863_);
lean_dec(v_n_2860_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray___redArg(lean_object* v_n_2865_, lean_object* v_v_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_mkPersistentArray___redArg(v_n_2865_, v_v_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray(lean_object* v_00_u03b1_2868_, lean_object* v_n_2869_, lean_object* v_v_2870_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_mkPersistentArray___redArg(v_n_2869_, v_v_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(lean_object* v_a_2872_, lean_object* v_a_2873_){
_start:
{
if (lean_obj_tag(v_a_2872_) == 0)
{
return v_a_2873_;
}
else
{
lean_object* v_head_2874_; lean_object* v_tail_2875_; lean_object* v___x_2876_; 
v_head_2874_ = lean_ctor_get(v_a_2872_, 0);
lean_inc(v_head_2874_);
v_tail_2875_ = lean_ctor_get(v_a_2872_, 1);
lean_inc(v_tail_2875_);
lean_dec_ref_known(v_a_2872_, 2);
v___x_2876_ = l_Lean_PersistentArray_push___redArg(v_a_2873_, v_head_2874_);
v_a_2872_ = v_tail_2875_;
v_a_2873_ = v___x_2876_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop(lean_object* v_00_u03b1_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_a_2879_, v_a_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27___redArg(lean_object* v_xs_2882_){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2883_ = lean_unsigned_to_nat(32u);
v___x_2884_ = lean_mk_empty_array_with_capacity(v___x_2883_);
lean_dec_ref(v___x_2884_);
v___x_2885_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_2886_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_xs_2882_, v___x_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27(lean_object* v_00_u03b1_2887_, lean_object* v_xs_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_List_toPArray_x27___redArg(v_xs_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object* v_xs_2890_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; uint8_t v___x_2894_; 
v___x_2891_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
v___x_2892_ = lean_unsigned_to_nat(0u);
v___x_2893_ = lean_array_get_size(v_xs_2890_);
v___x_2894_ = lean_nat_dec_lt(v___x_2892_, v___x_2893_);
if (v___x_2894_ == 0)
{
return v___x_2891_;
}
else
{
size_t v___x_2895_; size_t v___x_2896_; lean_object* v___x_2897_; 
v___x_2895_ = ((size_t)0ULL);
v___x_2896_ = lean_usize_of_nat(v___x_2893_);
v___x_2897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_2890_, v___x_2895_, v___x_2896_, v___x_2891_);
return v___x_2897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg___boxed(lean_object* v_xs_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Lean_Array_toPArray_x27___redArg(v_xs_2898_);
lean_dec_ref(v_xs_2898_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27(lean_object* v_00_u03b1_2900_, lean_object* v_xs_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_Array_toPArray_x27___redArg(v_xs_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___boxed(lean_object* v_00_u03b1_2903_, lean_object* v_xs_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Lean_Array_toPArray_x27(v_00_u03b1_2903_, v_xs_2904_);
lean_dec_ref(v_xs_2904_);
return v_res_2905_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_PersistentArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PersistentArray_initShift = _init_l_Lean_PersistentArray_initShift();
l_Lean_PersistentArray_branching = _init_l_Lean_PersistentArray_branching();
l_Lean_PersistentArray_tooBig = _init_l_Lean_PersistentArray_tooBig();
lean_mark_persistent(l_Lean_PersistentArray_tooBig);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_PersistentArray(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Fold(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Fold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_PersistentArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_PersistentArray(builtin);
}
#ifdef __cplusplus
}
#endif
