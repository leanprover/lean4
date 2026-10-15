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
lean_object* v_cs_483_; size_t v___x_484_; uint8_t v___x_485_; 
v_cs_483_ = lean_ctor_get(v_x_479_, 0);
v___x_484_ = ((size_t)32ULL);
v___x_485_ = lean_usize_dec_lt(v_x_480_, v___x_484_);
if (v___x_485_ == 0)
{
size_t v_j_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v_shift_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_j_486_ = lean_usize_shift_right(v_x_480_, v_x_481_);
v___x_487_ = ((size_t)1ULL);
v___x_488_ = lean_usize_shift_left(v___x_487_, v_x_481_);
v___x_489_ = ((size_t)5ULL);
v_shift_490_ = lean_usize_sub(v_x_481_, v___x_489_);
v___x_491_ = lean_usize_to_nat(v_j_486_);
v___x_492_ = lean_array_get_size(v_cs_483_);
v___x_493_ = lean_nat_dec_lt(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_502_; 
lean_inc_ref(v_cs_483_);
lean_dec(v___x_491_);
v_isSharedCheck_502_ = !lean_is_exclusive(v_x_479_);
if (v_isSharedCheck_502_ == 0)
{
lean_object* v_unused_503_; 
v_unused_503_ = lean_ctor_get(v_x_479_, 0);
lean_dec(v_unused_503_);
v___x_495_ = v_x_479_;
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
else
{
lean_dec(v_x_479_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_497_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_490_, v_x_482_);
v___x_498_ = lean_array_push(v_cs_483_, v___x_497_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_498_);
v___x_500_ = v___x_495_;
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
}
else
{
if (v___x_493_ == 0)
{
lean_dec(v___x_491_);
lean_dec_ref(v_x_482_);
return v_x_479_;
}
else
{
lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_517_; 
lean_inc_ref(v_cs_483_);
v_isSharedCheck_517_ = !lean_is_exclusive(v_x_479_);
if (v_isSharedCheck_517_ == 0)
{
lean_object* v_unused_518_; 
v_unused_518_ = lean_ctor_get(v_x_479_, 0);
lean_dec(v_unused_518_);
v___x_505_ = v_x_479_;
v_isShared_506_ = v_isSharedCheck_517_;
goto v_resetjp_504_;
}
else
{
lean_dec(v_x_479_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_517_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
size_t v___x_507_; size_t v_i_508_; lean_object* v_v_509_; lean_object* v___x_510_; lean_object* v_xs_x27_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_507_ = lean_usize_sub(v___x_488_, v___x_487_);
v_i_508_ = lean_usize_land(v_x_480_, v___x_507_);
v_v_509_ = lean_array_fget(v_cs_483_, v___x_491_);
v___x_510_ = lean_box(0);
v_xs_x27_511_ = lean_array_fset(v_cs_483_, v___x_491_, v___x_510_);
v___x_512_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_v_509_, v_i_508_, v_shift_490_, v_x_482_);
v___x_513_ = lean_array_fset(v_xs_x27_511_, v___x_491_, v___x_512_);
lean_dec(v___x_491_);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v___x_513_);
v___x_515_ = v___x_505_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v___x_513_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
}
else
{
lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_527_; 
lean_inc_ref(v_cs_483_);
v_isSharedCheck_527_ = !lean_is_exclusive(v_x_479_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v_x_479_, 0);
lean_dec(v_unused_528_);
v___x_520_ = v_x_479_;
v_isShared_521_ = v_isSharedCheck_527_;
goto v_resetjp_519_;
}
else
{
lean_dec(v_x_479_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_527_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set_tag(v___x_520_, 1);
lean_ctor_set(v___x_520_, 0, v_x_482_);
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_x_482_);
v___x_523_ = v_reuseFailAlloc_526_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = lean_array_push(v_cs_483_, v___x_523_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v___x_524_);
return v___x_525_;
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg___boxed(lean_object* v_x_529_, lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
size_t v_x_102__boxed_533_; size_t v_x_103__boxed_534_; lean_object* v_res_535_; 
v_x_102__boxed_533_ = lean_unbox_usize(v_x_530_);
lean_dec(v_x_530_);
v_x_103__boxed_534_ = lean_unbox_usize(v_x_531_);
lean_dec(v_x_531_);
v_res_535_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_529_, v_x_102__boxed_533_, v_x_103__boxed_534_, v_x_532_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf(lean_object* v_00_u03b1_536_, lean_object* v_x_537_, size_t v_x_538_, size_t v_x_539_, lean_object* v_x_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_537_, v_x_538_, v_x_539_, v_x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___boxed(lean_object* v_00_u03b1_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
size_t v_x_196__boxed_547_; size_t v_x_197__boxed_548_; lean_object* v_res_549_; 
v_x_196__boxed_547_ = lean_unbox_usize(v_x_544_);
lean_dec(v_x_544_);
v_x_197__boxed_548_ = lean_unbox_usize(v_x_545_);
lean_dec(v_x_545_);
v_res_549_ = l_Lean_PersistentArray_insertNewLeaf(v_00_u03b1_542_, v_x_543_, v_x_196__boxed_547_, v_x_197__boxed_548_, v_x_546_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail___redArg(lean_object* v_t_552_){
_start:
{
lean_object* v_root_553_; lean_object* v_tail_554_; lean_object* v_size_555_; size_t v_shift_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_583_; 
v_root_553_ = lean_ctor_get(v_t_552_, 0);
v_tail_554_ = lean_ctor_get(v_t_552_, 1);
v_size_555_ = lean_ctor_get(v_t_552_, 2);
v_shift_556_ = lean_ctor_get_usize(v_t_552_, 4);
v_isSharedCheck_583_ = !lean_is_exclusive(v_t_552_);
if (v_isSharedCheck_583_ == 0)
{
lean_object* v_unused_584_; 
v_unused_584_ = lean_ctor_get(v_t_552_, 3);
lean_dec(v_unused_584_);
v___x_558_ = v_t_552_;
v_isShared_559_ = v_isSharedCheck_583_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_size_555_);
lean_inc(v_tail_554_);
lean_inc(v_root_553_);
lean_dec(v_t_552_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_583_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
size_t v___x_560_; size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_560_ = ((size_t)1ULL);
v___x_561_ = ((size_t)5ULL);
v___x_562_ = lean_usize_add(v_shift_556_, v___x_561_);
v___x_563_ = lean_usize_shift_left(v___x_560_, v___x_562_);
v___x_564_ = lean_usize_to_nat(v___x_563_);
v___x_565_ = lean_nat_dec_le(v_size_555_, v___x_564_);
lean_dec(v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v_n_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_566_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
v_n_567_ = lean_array_push(v___x_566_, v_root_553_);
v___x_568_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_556_, v_tail_554_);
v___x_569_ = lean_array_push(v_n_567_, v___x_568_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
v___x_571_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
lean_inc(v_size_555_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 3, v_size_555_);
lean_ctor_set(v___x_558_, 1, v___x_571_);
lean_ctor_set(v___x_558_, 0, v___x_570_);
v___x_573_ = v___x_558_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_570_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_size_555_);
lean_ctor_set(v_reuseFailAlloc_574_, 3, v_size_555_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_ctor_set_usize(v___x_573_, 4, v___x_562_);
return v___x_573_;
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; size_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = lean_nat_sub(v_size_555_, v___x_575_);
v___x_577_ = lean_usize_of_nat(v___x_576_);
lean_dec(v___x_576_);
v___x_578_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_root_553_, v___x_577_, v_shift_556_, v_tail_554_);
v___x_579_ = lean_obj_once(&l_Lean_PersistentArray_mkEmptyArray___closed__0, &l_Lean_PersistentArray_mkEmptyArray___closed__0_once, _init_l_Lean_PersistentArray_mkEmptyArray___closed__0);
lean_inc(v_size_555_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 3, v_size_555_);
lean_ctor_set(v___x_558_, 1, v___x_579_);
lean_ctor_set(v___x_558_, 0, v___x_578_);
v___x_581_ = v___x_558_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_size_555_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v_size_555_);
lean_ctor_set_usize(v_reuseFailAlloc_582_, 4, v_shift_556_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail(lean_object* v_00_u03b1_585_, lean_object* v_t_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_PersistentArray_mkNewTail___redArg(v_t_586_);
return v___x_587_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__0(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v___x_588_ = l_System_Platform_numBits;
v___x_589_ = lean_unsigned_to_nat(2u);
v___x_590_ = lean_nat_pow(v___x_589_, v___x_588_);
return v___x_590_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__1(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_unsigned_to_nat(3u);
v___x_592_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__0, &l_Lean_PersistentArray_tooBig___closed__0_once, _init_l_Lean_PersistentArray_tooBig___closed__0);
v___x_593_ = lean_nat_shiftr(v___x_592_, v___x_591_);
return v___x_593_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig(void){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__1, &l_Lean_PersistentArray_tooBig___closed__1_once, _init_l_Lean_PersistentArray_tooBig___closed__1);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push___redArg(lean_object* v_t_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_root_597_; lean_object* v_tail_598_; lean_object* v_size_599_; size_t v_shift_600_; lean_object* v_tailOff_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_617_; 
v_root_597_ = lean_ctor_get(v_t_595_, 0);
v_tail_598_ = lean_ctor_get(v_t_595_, 1);
v_size_599_ = lean_ctor_get(v_t_595_, 2);
v_shift_600_ = lean_ctor_get_usize(v_t_595_, 4);
v_tailOff_601_ = lean_ctor_get(v_t_595_, 3);
v_isSharedCheck_617_ = !lean_is_exclusive(v_t_595_);
if (v_isSharedCheck_617_ == 0)
{
v___x_603_ = v_t_595_;
v_isShared_604_ = v_isSharedCheck_617_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_tailOff_601_);
lean_inc(v_size_599_);
lean_inc(v_tail_598_);
lean_inc(v_root_597_);
lean_dec(v_t_595_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_617_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_r_609_; 
v___x_605_ = lean_array_push(v_tail_598_, v_a_596_);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v_size_599_, v___x_606_);
lean_inc_ref(v___x_605_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 2, v___x_607_);
lean_ctor_set(v___x_603_, 1, v___x_605_);
v_r_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_root_597_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_605_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_tailOff_601_);
lean_ctor_set_usize(v_reuseFailAlloc_616_, 4, v_shift_600_);
v_r_609_ = v_reuseFailAlloc_616_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_array_get_size(v___x_605_);
lean_dec_ref(v___x_605_);
v___x_611_ = lean_unsigned_to_nat(32u);
v___x_612_ = lean_nat_dec_lt(v___x_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = l_Lean_PersistentArray_tooBig;
v___x_614_ = lean_nat_dec_le(v___x_613_, v_size_599_);
lean_dec(v_size_599_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_PersistentArray_mkNewTail___redArg(v_r_609_);
return v___x_615_;
}
else
{
return v_r_609_;
}
}
else
{
lean_dec(v_size_599_);
return v_r_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push(lean_object* v_00_u03b1_618_, lean_object* v_t_619_, lean_object* v_a_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_PersistentArray_push___redArg(v_t_619_, v_a_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg(){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(32u);
v___x_624_ = lean_mk_empty_array_with_capacity(v___x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg___boxed(lean_object* v___dummy_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
return v_res_626_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0(void){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___redArg();
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_object* v_00_u03b1_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_630_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___x_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf___redArg(lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_633_) == 0)
{
lean_object* v_cs_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_684_; 
v_cs_634_ = lean_ctor_get(v_x_633_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_633_);
if (v_isSharedCheck_684_ == 0)
{
v___x_636_ = v_x_633_;
v_isShared_637_ = v_isSharedCheck_684_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_cs_634_);
lean_dec(v_x_633_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_684_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_array_get_size(v_cs_634_);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_nat_dec_eq(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; lean_object* v_idx_642_; lean_object* v_last_643_; lean_object* v___x_644_; lean_object* v_fst_645_; 
v___x_641_ = lean_unsigned_to_nat(1u);
v_idx_642_ = lean_nat_sub(v___x_638_, v___x_641_);
v_last_643_ = lean_array_fget_borrowed(v_cs_634_, v_idx_642_);
lean_inc(v_last_643_);
v___x_644_ = l_Lean_PersistentArray_popLeaf___redArg(v_last_643_);
v_fst_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_fst_645_);
if (lean_obj_tag(v_fst_645_) == 0)
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
lean_dec(v_idx_642_);
lean_del_object(v___x_636_);
lean_dec_ref(v_cs_634_);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; lean_object* v_unused_655_; 
v_unused_654_ = lean_ctor_get(v___x_644_, 1);
lean_dec(v_unused_654_);
v_unused_655_ = lean_ctor_get(v___x_644_, 0);
lean_dec(v_unused_655_);
v___x_647_ = v___x_644_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_dec(v___x_644_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_fst_645_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
else
{
lean_object* v_snd_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_681_; 
v_snd_656_ = lean_ctor_get(v___x_644_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v___x_644_, 0);
lean_dec(v_unused_682_);
v___x_658_ = v___x_644_;
v_isShared_659_ = v_isSharedCheck_681_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_snd_656_);
lean_dec(v___x_644_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_681_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v_cs_x27_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_660_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v_cs_x27_661_ = lean_array_fset(v_cs_634_, v_idx_642_, v___x_660_);
v___x_662_ = lean_array_get_size(v_snd_656_);
v___x_663_ = lean_nat_dec_eq(v___x_662_, v___x_639_);
if (v___x_663_ == 0)
{
lean_object* v___x_665_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set(v___x_636_, 0, v_snd_656_);
v___x_665_ = v___x_636_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_snd_656_);
v___x_665_ = v_reuseFailAlloc_670_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = lean_array_fset(v_cs_x27_661_, v_idx_642_, v___x_665_);
lean_dec(v_idx_642_);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_666_);
v___x_668_ = v___x_658_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_fst_645_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v_cs_x27_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
lean_dec(v_snd_656_);
lean_dec(v_idx_642_);
lean_del_object(v___x_636_);
v_cs_x27_671_ = lean_array_pop(v_cs_x27_661_);
v___x_672_ = lean_array_get_size(v_cs_x27_671_);
v___x_673_ = lean_nat_dec_eq(v___x_672_, v___x_639_);
if (v___x_673_ == 0)
{
lean_object* v___x_675_; 
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v_cs_x27_671_);
v___x_675_ = v___x_658_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_fst_645_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_cs_x27_671_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
else
{
lean_object* v___x_677_; lean_object* v___x_679_; 
lean_dec_ref(v_cs_x27_671_);
v___x_677_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 1, v___x_677_);
v___x_679_ = v___x_658_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_fst_645_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
else
{
lean_object* v___x_683_; 
lean_del_object(v___x_636_);
lean_dec_ref(v_cs_634_);
v___x_683_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
return v___x_683_;
}
}
}
else
{
lean_object* v_vs_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_vs_685_ = lean_ctor_get(v_x_633_, 0);
lean_inc_ref(v_vs_685_);
lean_dec_ref_known(v_x_633_, 1);
v___x_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_686_, 0, v_vs_685_);
v___x_687_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray___closed__0);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf(lean_object* v_00_u03b1_689_, lean_object* v_x_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_PersistentArray_popLeaf___redArg(v_x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop___redArg(lean_object* v_t_692_){
_start:
{
lean_object* v_root_693_; lean_object* v_tail_694_; lean_object* v_size_695_; size_t v_shift_696_; lean_object* v_tailOff_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_root_693_ = lean_ctor_get(v_t_692_, 0);
v_tail_694_ = lean_ctor_get(v_t_692_, 1);
v_size_695_ = lean_ctor_get(v_t_692_, 2);
v_shift_696_ = lean_ctor_get_usize(v_t_692_, 4);
v_tailOff_697_ = lean_ctor_get(v_t_692_, 3);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_array_get_size(v_tail_694_);
v___x_700_ = lean_nat_dec_lt(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v_fst_702_; 
lean_inc_ref(v_root_693_);
v___x_701_ = l_Lean_PersistentArray_popLeaf___redArg(v_root_693_);
v_fst_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_fst_702_);
if (lean_obj_tag(v_fst_702_) == 0)
{
lean_dec_ref(v___x_701_);
return v_t_692_;
}
else
{
lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_735_; 
lean_inc(v_size_695_);
v_isSharedCheck_735_ = !lean_is_exclusive(v_t_692_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; lean_object* v_unused_737_; lean_object* v_unused_738_; lean_object* v_unused_739_; 
v_unused_736_ = lean_ctor_get(v_t_692_, 3);
lean_dec(v_unused_736_);
v_unused_737_ = lean_ctor_get(v_t_692_, 2);
lean_dec(v_unused_737_);
v_unused_738_ = lean_ctor_get(v_t_692_, 1);
lean_dec(v_unused_738_);
v_unused_739_ = lean_ctor_get(v_t_692_, 0);
lean_dec(v_unused_739_);
v___x_704_ = v_t_692_;
v_isShared_705_ = v_isSharedCheck_735_;
goto v_resetjp_703_;
}
else
{
lean_dec(v_t_692_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_735_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v_snd_706_; lean_object* v_val_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_734_; 
v_snd_706_ = lean_ctor_get(v___x_701_, 1);
lean_inc(v_snd_706_);
lean_dec_ref(v___x_701_);
v_val_707_ = lean_ctor_get(v_fst_702_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_fst_702_);
if (v_isSharedCheck_734_ == 0)
{
v___x_709_ = v_fst_702_;
v_isShared_710_ = v_isSharedCheck_734_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_val_707_);
lean_dec(v_fst_702_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_734_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v_last_711_; lean_object* v___x_712_; lean_object* v_newSize_713_; lean_object* v___x_714_; lean_object* v_newTailOff_715_; uint8_t v___y_717_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_last_711_ = lean_array_pop(v_val_707_);
v___x_712_ = lean_unsigned_to_nat(1u);
v_newSize_713_ = lean_nat_sub(v_size_695_, v___x_712_);
lean_dec(v_size_695_);
v___x_714_ = lean_array_get_size(v_last_711_);
v_newTailOff_715_ = lean_nat_sub(v_newSize_713_, v___x_714_);
v___x_730_ = lean_array_get_size(v_snd_706_);
v___x_731_ = lean_nat_dec_eq(v___x_730_, v___x_712_);
if (v___x_731_ == 0)
{
v___y_717_ = v___x_731_;
goto v___jp_716_;
}
else
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_array_fget_borrowed(v_snd_706_, v___x_698_);
v___x_733_ = l_Lean_PersistentArrayNode_isNode___redArg(v___x_732_);
v___y_717_ = v___x_733_;
goto v___jp_716_;
}
v___jp_716_:
{
if (v___y_717_ == 0)
{
lean_object* v___x_719_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 0);
lean_ctor_set(v___x_709_, 0, v_snd_706_);
v___x_719_ = v___x_709_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_snd_706_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 3, v_newTailOff_715_);
lean_ctor_set(v___x_704_, 2, v_newSize_713_);
lean_ctor_set(v___x_704_, 1, v_last_711_);
lean_ctor_set(v___x_704_, 0, v___x_719_);
v___x_721_ = v___x_704_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_last_711_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_newSize_713_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_newTailOff_715_);
lean_ctor_set_usize(v_reuseFailAlloc_722_, 4, v_shift_696_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
lean_object* v___x_724_; size_t v___x_725_; size_t v___x_726_; lean_object* v___x_728_; 
lean_del_object(v___x_709_);
v___x_724_ = lean_array_fget(v_snd_706_, v___x_698_);
lean_dec(v_snd_706_);
v___x_725_ = ((size_t)5ULL);
v___x_726_ = lean_usize_sub(v_shift_696_, v___x_725_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 3, v_newTailOff_715_);
lean_ctor_set(v___x_704_, 2, v_newSize_713_);
lean_ctor_set(v___x_704_, 1, v_last_711_);
lean_ctor_set(v___x_704_, 0, v___x_724_);
v___x_728_ = v___x_704_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v_last_711_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_newSize_713_);
lean_ctor_set(v_reuseFailAlloc_729_, 3, v_newTailOff_715_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_ctor_set_usize(v___x_728_, 4, v___x_726_);
return v___x_728_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_749_; 
lean_inc(v_tailOff_697_);
lean_inc(v_size_695_);
lean_inc_ref(v_tail_694_);
lean_inc_ref(v_root_693_);
v_isSharedCheck_749_ = !lean_is_exclusive(v_t_692_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; lean_object* v_unused_751_; lean_object* v_unused_752_; lean_object* v_unused_753_; 
v_unused_750_ = lean_ctor_get(v_t_692_, 3);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_t_692_, 2);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_t_692_, 1);
lean_dec(v_unused_752_);
v_unused_753_ = lean_ctor_get(v_t_692_, 0);
lean_dec(v_unused_753_);
v___x_741_ = v_t_692_;
v_isShared_742_ = v_isSharedCheck_749_;
goto v_resetjp_740_;
}
else
{
lean_dec(v_t_692_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_749_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_743_ = lean_array_pop(v_tail_694_);
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = lean_nat_sub(v_size_695_, v___x_744_);
lean_dec(v_size_695_);
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 2, v___x_745_);
lean_ctor_set(v___x_741_, 1, v___x_743_);
v___x_747_ = v___x_741_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_root_693_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v___x_743_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_tailOff_697_);
lean_ctor_set_usize(v_reuseFailAlloc_748_, 4, v_shift_696_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop(lean_object* v_00_u03b1_754_, lean_object* v_t_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_PersistentArray_pop___redArg(v_t_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(lean_object* v_inst_757_, lean_object* v_f_758_, lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_759_) == 0)
{
lean_object* v_toApplicative_761_; lean_object* v_cs_762_; lean_object* v_toPure_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_toApplicative_761_ = lean_ctor_get(v_inst_757_, 0);
v_cs_762_ = lean_ctor_get(v_x_759_, 0);
lean_inc_ref(v_cs_762_);
lean_dec_ref_known(v_x_759_, 1);
v_toPure_763_ = lean_ctor_get(v_toApplicative_761_, 1);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_array_get_size(v_cs_762_);
v___x_766_ = lean_nat_dec_lt(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_inc(v_toPure_763_);
lean_dec_ref(v_cs_762_);
lean_dec(v_f_758_);
lean_dec_ref(v_inst_757_);
v___x_767_ = lean_apply_2(v_toPure_763_, lean_box(0), v_x_760_);
return v___x_767_;
}
else
{
lean_object* v___f_768_; uint8_t v___x_769_; 
lean_inc_ref(v_inst_757_);
v___f_768_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_768_, 0, v_inst_757_);
lean_closure_set(v___f_768_, 1, v_f_758_);
v___x_769_ = lean_nat_dec_le(v___x_765_, v___x_765_);
if (v___x_769_ == 0)
{
if (v___x_766_ == 0)
{
lean_object* v___x_770_; 
lean_inc(v_toPure_763_);
lean_dec_ref(v___f_768_);
lean_dec_ref(v_cs_762_);
lean_dec_ref(v_inst_757_);
v___x_770_ = lean_apply_2(v_toPure_763_, lean_box(0), v_x_760_);
return v___x_770_;
}
else
{
size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_771_ = ((size_t)0ULL);
v___x_772_ = lean_usize_of_nat(v___x_765_);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_757_, v___f_768_, v_cs_762_, v___x_771_, v___x_772_, v_x_760_);
return v___x_773_;
}
}
else
{
size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((size_t)0ULL);
v___x_775_ = lean_usize_of_nat(v___x_765_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_757_, v___f_768_, v_cs_762_, v___x_774_, v___x_775_, v_x_760_);
return v___x_776_;
}
}
}
else
{
lean_object* v_toApplicative_777_; lean_object* v_vs_778_; lean_object* v_toPure_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_toApplicative_777_ = lean_ctor_get(v_inst_757_, 0);
v_vs_778_ = lean_ctor_get(v_x_759_, 0);
lean_inc_ref(v_vs_778_);
lean_dec_ref_known(v_x_759_, 1);
v_toPure_779_ = lean_ctor_get(v_toApplicative_777_, 1);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_array_get_size(v_vs_778_);
v___x_782_ = lean_nat_dec_lt(v___x_780_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; 
lean_inc(v_toPure_779_);
lean_dec_ref(v_vs_778_);
lean_dec(v_f_758_);
lean_dec_ref(v_inst_757_);
v___x_783_ = lean_apply_2(v_toPure_779_, lean_box(0), v_x_760_);
return v___x_783_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = lean_nat_dec_le(v___x_781_, v___x_781_);
if (v___x_784_ == 0)
{
if (v___x_782_ == 0)
{
lean_object* v___x_785_; 
lean_inc(v_toPure_779_);
lean_dec_ref(v_vs_778_);
lean_dec(v_f_758_);
lean_dec_ref(v_inst_757_);
v___x_785_ = lean_apply_2(v_toPure_779_, lean_box(0), v_x_760_);
return v___x_785_;
}
else
{
size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; 
v___x_786_ = ((size_t)0ULL);
v___x_787_ = lean_usize_of_nat(v___x_781_);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_757_, v_f_758_, v_vs_778_, v___x_786_, v___x_787_, v_x_760_);
return v___x_788_;
}
}
else
{
size_t v___x_789_; size_t v___x_790_; lean_object* v___x_791_; 
v___x_789_ = ((size_t)0ULL);
v___x_790_ = lean_usize_of_nat(v___x_781_);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_757_, v_f_758_, v_vs_778_, v___x_789_, v___x_790_, v_x_760_);
return v___x_791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0(lean_object* v_inst_792_, lean_object* v_f_793_, lean_object* v_b_794_, lean_object* v_c_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_792_, v_f_793_, v_c_795_, v_b_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux(lean_object* v_00_u03b1_797_, lean_object* v_m_798_, lean_object* v_inst_799_, lean_object* v_00_u03b2_800_, lean_object* v_f_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_799_, v_f_801_, v_x_802_, v_x_803_);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(lean_object* v_toApplicative_805_, lean_object* v_j_806_, lean_object* v_cs_807_, lean_object* v_inst_808_, lean_object* v___f_809_, lean_object* v_b_810_){
_start:
{
lean_object* v_toPure_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v_toPure_811_ = lean_ctor_get(v_toApplicative_805_, 1);
lean_inc(v_toPure_811_);
lean_dec_ref(v_toApplicative_805_);
v___x_812_ = lean_unsigned_to_nat(1u);
v___x_813_ = lean_nat_add(v_j_806_, v___x_812_);
v___x_814_ = lean_array_get_size(v_cs_807_);
v___x_815_ = lean_nat_dec_lt(v___x_813_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
lean_dec(v___x_813_);
lean_dec(v___f_809_);
lean_dec_ref(v_inst_808_);
lean_dec_ref(v_cs_807_);
v___x_816_ = lean_apply_2(v_toPure_811_, lean_box(0), v_b_810_);
return v___x_816_;
}
else
{
uint8_t v___x_817_; 
v___x_817_ = lean_nat_dec_le(v___x_814_, v___x_814_);
if (v___x_817_ == 0)
{
if (v___x_815_ == 0)
{
lean_object* v___x_818_; 
lean_dec(v___x_813_);
lean_dec(v___f_809_);
lean_dec_ref(v_inst_808_);
lean_dec_ref(v_cs_807_);
v___x_818_ = lean_apply_2(v_toPure_811_, lean_box(0), v_b_810_);
return v___x_818_;
}
else
{
size_t v___x_819_; size_t v___x_820_; lean_object* v___x_821_; 
lean_dec(v_toPure_811_);
v___x_819_ = lean_usize_of_nat(v___x_813_);
lean_dec(v___x_813_);
v___x_820_ = lean_usize_of_nat(v___x_814_);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_808_, v___f_809_, v_cs_807_, v___x_819_, v___x_820_, v_b_810_);
return v___x_821_;
}
}
else
{
size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
lean_dec(v_toPure_811_);
v___x_822_ = lean_usize_of_nat(v___x_813_);
lean_dec(v___x_813_);
v___x_823_ = lean_usize_of_nat(v___x_814_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_808_, v___f_809_, v_cs_807_, v___x_822_, v___x_823_, v_b_810_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_825_, lean_object* v_j_826_, lean_object* v_cs_827_, lean_object* v_inst_828_, lean_object* v___f_829_, lean_object* v_b_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(v_toApplicative_825_, v_j_826_, v_cs_827_, v_inst_828_, v___f_829_, v_b_830_);
lean_dec(v_j_826_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(lean_object* v_inst_832_, lean_object* v_f_833_, lean_object* v_x_834_, size_t v_x_835_, size_t v_x_836_, lean_object* v_x_837_){
_start:
{
if (lean_obj_tag(v_x_834_) == 0)
{
lean_object* v_toApplicative_838_; lean_object* v_toBind_839_; lean_object* v_cs_840_; lean_object* v___f_841_; lean_object* v___x_842_; size_t v___x_843_; lean_object* v_j_844_; lean_object* v___f_845_; lean_object* v___x_846_; size_t v___x_847_; size_t v___x_848_; size_t v___x_849_; size_t v___x_850_; size_t v___x_851_; size_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v_toApplicative_838_ = lean_ctor_get(v_inst_832_, 0);
v_toBind_839_ = lean_ctor_get(v_inst_832_, 1);
lean_inc(v_toBind_839_);
v_cs_840_ = lean_ctor_get(v_x_834_, 0);
lean_inc_ref_n(v_cs_840_, 2);
lean_dec_ref_known(v_x_834_, 1);
lean_inc(v_f_833_);
lean_inc_ref_n(v_inst_832_, 2);
v___f_841_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_841_, 0, v_inst_832_);
lean_closure_set(v___f_841_, 1, v_f_833_);
v___x_842_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_843_ = lean_usize_shift_right(v_x_835_, v_x_836_);
v_j_844_ = lean_usize_to_nat(v___x_843_);
lean_inc(v_j_844_);
lean_inc_ref(v_toApplicative_838_);
v___f_845_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_845_, 0, v_toApplicative_838_);
lean_closure_set(v___f_845_, 1, v_j_844_);
lean_closure_set(v___f_845_, 2, v_cs_840_);
lean_closure_set(v___f_845_, 3, v_inst_832_);
lean_closure_set(v___f_845_, 4, v___f_841_);
v___x_846_ = lean_array_get(v___x_842_, v_cs_840_, v_j_844_);
lean_dec(v_j_844_);
lean_dec_ref(v_cs_840_);
v___x_847_ = ((size_t)1ULL);
v___x_848_ = lean_usize_shift_left(v___x_847_, v_x_836_);
v___x_849_ = lean_usize_sub(v___x_848_, v___x_847_);
v___x_850_ = lean_usize_land(v_x_835_, v___x_849_);
v___x_851_ = ((size_t)5ULL);
v___x_852_ = lean_usize_sub(v_x_836_, v___x_851_);
v___x_853_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_832_, v_f_833_, v___x_846_, v___x_850_, v___x_852_, v_x_837_);
v___x_854_ = lean_apply_4(v_toBind_839_, lean_box(0), lean_box(0), v___x_853_, v___f_845_);
return v___x_854_;
}
else
{
lean_object* v_toApplicative_855_; lean_object* v_vs_856_; lean_object* v_toPure_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_toApplicative_855_ = lean_ctor_get(v_inst_832_, 0);
v_vs_856_ = lean_ctor_get(v_x_834_, 0);
lean_inc_ref(v_vs_856_);
lean_dec_ref_known(v_x_834_, 1);
v_toPure_857_ = lean_ctor_get(v_toApplicative_855_, 1);
v___x_858_ = lean_usize_to_nat(v_x_835_);
v___x_859_ = lean_array_get_size(v_vs_856_);
v___x_860_ = lean_nat_dec_lt(v___x_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
lean_inc(v_toPure_857_);
lean_dec(v___x_858_);
lean_dec_ref(v_vs_856_);
lean_dec(v_f_833_);
lean_dec_ref(v_inst_832_);
v___x_861_ = lean_apply_2(v_toPure_857_, lean_box(0), v_x_837_);
return v___x_861_;
}
else
{
uint8_t v___x_862_; 
v___x_862_ = lean_nat_dec_le(v___x_859_, v___x_859_);
if (v___x_862_ == 0)
{
if (v___x_860_ == 0)
{
lean_object* v___x_863_; 
lean_inc(v_toPure_857_);
lean_dec(v___x_858_);
lean_dec_ref(v_vs_856_);
lean_dec(v_f_833_);
lean_dec_ref(v_inst_832_);
v___x_863_ = lean_apply_2(v_toPure_857_, lean_box(0), v_x_837_);
return v___x_863_;
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_usize_of_nat(v___x_858_);
lean_dec(v___x_858_);
v___x_865_ = lean_usize_of_nat(v___x_859_);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_832_, v_f_833_, v_vs_856_, v___x_864_, v___x_865_, v_x_837_);
return v___x_866_;
}
}
else
{
size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; 
v___x_867_ = lean_usize_of_nat(v___x_858_);
lean_dec(v___x_858_);
v___x_868_ = lean_usize_of_nat(v___x_859_);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_832_, v_f_833_, v_vs_856_, v___x_867_, v___x_868_, v_x_837_);
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___boxed(lean_object* v_inst_870_, lean_object* v_f_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_x_875_){
_start:
{
size_t v_x_207__boxed_876_; size_t v_x_208__boxed_877_; lean_object* v_res_878_; 
v_x_207__boxed_876_ = lean_unbox_usize(v_x_873_);
lean_dec(v_x_873_);
v_x_208__boxed_877_ = lean_unbox_usize(v_x_874_);
lean_dec(v_x_874_);
v_res_878_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_870_, v_f_871_, v_x_872_, v_x_207__boxed_876_, v_x_208__boxed_877_, v_x_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(lean_object* v_00_u03b1_879_, lean_object* v_m_880_, lean_object* v_inst_881_, lean_object* v_00_u03b2_882_, lean_object* v_f_883_, lean_object* v_x_884_, size_t v_x_885_, size_t v_x_886_, lean_object* v_x_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_881_, v_f_883_, v_x_884_, v_x_885_, v_x_886_, v_x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___boxed(lean_object* v_00_u03b1_889_, lean_object* v_m_890_, lean_object* v_inst_891_, lean_object* v_00_u03b2_892_, lean_object* v_f_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_){
_start:
{
size_t v_x_276__boxed_898_; size_t v_x_277__boxed_899_; lean_object* v_res_900_; 
v_x_276__boxed_898_ = lean_unbox_usize(v_x_895_);
lean_dec(v_x_895_);
v_x_277__boxed_899_ = lean_unbox_usize(v_x_896_);
lean_dec(v_x_896_);
v_res_900_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(v_00_u03b1_889_, v_m_890_, v_inst_891_, v_00_u03b2_892_, v_f_893_, v_x_894_, v_x_276__boxed_898_, v_x_277__boxed_899_, v_x_897_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0(lean_object* v_toApplicative_901_, lean_object* v_tail_902_, lean_object* v___x_903_, lean_object* v_inst_904_, lean_object* v_f_905_, lean_object* v_b_906_){
_start:
{
lean_object* v_toPure_907_; lean_object* v___x_908_; uint8_t v___x_909_; 
v_toPure_907_ = lean_ctor_get(v_toApplicative_901_, 1);
lean_inc(v_toPure_907_);
lean_dec_ref(v_toApplicative_901_);
v___x_908_ = lean_array_get_size(v_tail_902_);
v___x_909_ = lean_nat_dec_lt(v___x_903_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; 
lean_dec(v_f_905_);
lean_dec_ref(v_inst_904_);
lean_dec_ref(v_tail_902_);
v___x_910_ = lean_apply_2(v_toPure_907_, lean_box(0), v_b_906_);
return v___x_910_;
}
else
{
uint8_t v___x_911_; 
v___x_911_ = lean_nat_dec_le(v___x_908_, v___x_908_);
if (v___x_911_ == 0)
{
if (v___x_909_ == 0)
{
lean_object* v___x_912_; 
lean_dec(v_f_905_);
lean_dec_ref(v_inst_904_);
lean_dec_ref(v_tail_902_);
v___x_912_ = lean_apply_2(v_toPure_907_, lean_box(0), v_b_906_);
return v___x_912_;
}
else
{
size_t v___x_913_; size_t v___x_914_; lean_object* v___x_915_; 
lean_dec(v_toPure_907_);
v___x_913_ = ((size_t)0ULL);
v___x_914_ = lean_usize_of_nat(v___x_908_);
v___x_915_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_904_, v_f_905_, v_tail_902_, v___x_913_, v___x_914_, v_b_906_);
return v___x_915_;
}
}
else
{
size_t v___x_916_; size_t v___x_917_; lean_object* v___x_918_; 
lean_dec(v_toPure_907_);
v___x_916_ = ((size_t)0ULL);
v___x_917_ = lean_usize_of_nat(v___x_908_);
v___x_918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_904_, v_f_905_, v_tail_902_, v___x_916_, v___x_917_, v_b_906_);
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed(lean_object* v_toApplicative_919_, lean_object* v_tail_920_, lean_object* v___x_921_, lean_object* v_inst_922_, lean_object* v_f_923_, lean_object* v_b_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_PersistentArray_foldlM___redArg___lam__0(v_toApplicative_919_, v_tail_920_, v___x_921_, v_inst_922_, v_f_923_, v_b_924_);
lean_dec(v___x_921_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object* v_inst_926_, lean_object* v_t_927_, lean_object* v_f_928_, lean_object* v_init_929_, lean_object* v_start_930_){
_start:
{
lean_object* v_toApplicative_931_; lean_object* v_toBind_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v_toApplicative_931_ = lean_ctor_get(v_inst_926_, 0);
v_toBind_932_ = lean_ctor_get(v_inst_926_, 1);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_nat_dec_eq(v_start_930_, v___x_933_);
if (v___x_934_ == 0)
{
lean_object* v_root_935_; lean_object* v_tail_936_; size_t v_shift_937_; lean_object* v_tailOff_938_; uint8_t v___x_939_; 
v_root_935_ = lean_ctor_get(v_t_927_, 0);
lean_inc_ref(v_root_935_);
v_tail_936_ = lean_ctor_get(v_t_927_, 1);
lean_inc_ref(v_tail_936_);
v_shift_937_ = lean_ctor_get_usize(v_t_927_, 4);
v_tailOff_938_ = lean_ctor_get(v_t_927_, 3);
lean_inc(v_tailOff_938_);
lean_dec_ref(v_t_927_);
v___x_939_ = lean_nat_dec_le(v_tailOff_938_, v_start_930_);
if (v___x_939_ == 0)
{
lean_object* v___f_940_; size_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_inc(v_toBind_932_);
lean_dec(v_tailOff_938_);
lean_inc(v_f_928_);
lean_inc_ref(v_inst_926_);
lean_inc_ref(v_toApplicative_931_);
v___f_940_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_940_, 0, v_toApplicative_931_);
lean_closure_set(v___f_940_, 1, v_tail_936_);
lean_closure_set(v___f_940_, 2, v___x_933_);
lean_closure_set(v___f_940_, 3, v_inst_926_);
lean_closure_set(v___f_940_, 4, v_f_928_);
v___x_941_ = lean_usize_of_nat(v_start_930_);
v___x_942_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_926_, v_f_928_, v_root_935_, v___x_941_, v_shift_937_, v_init_929_);
v___x_943_ = lean_apply_4(v_toBind_932_, lean_box(0), lean_box(0), v___x_942_, v___f_940_);
return v___x_943_;
}
else
{
lean_object* v_toPure_944_; lean_object* v___x_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
lean_dec_ref(v_root_935_);
v_toPure_944_ = lean_ctor_get(v_toApplicative_931_, 1);
v___x_945_ = lean_nat_sub(v_start_930_, v_tailOff_938_);
lean_dec(v_tailOff_938_);
v___x_946_ = lean_array_get_size(v_tail_936_);
v___x_947_ = lean_nat_dec_lt(v___x_945_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; 
lean_inc(v_toPure_944_);
lean_dec(v___x_945_);
lean_dec_ref(v_tail_936_);
lean_dec(v_f_928_);
lean_dec_ref(v_inst_926_);
v___x_948_ = lean_apply_2(v_toPure_944_, lean_box(0), v_init_929_);
return v___x_948_;
}
else
{
uint8_t v___x_949_; 
v___x_949_ = lean_nat_dec_le(v___x_946_, v___x_946_);
if (v___x_949_ == 0)
{
if (v___x_947_ == 0)
{
lean_object* v___x_950_; 
lean_inc(v_toPure_944_);
lean_dec(v___x_945_);
lean_dec_ref(v_tail_936_);
lean_dec(v_f_928_);
lean_dec_ref(v_inst_926_);
v___x_950_ = lean_apply_2(v_toPure_944_, lean_box(0), v_init_929_);
return v___x_950_;
}
else
{
size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_usize_of_nat(v___x_945_);
lean_dec(v___x_945_);
v___x_952_ = lean_usize_of_nat(v___x_946_);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_926_, v_f_928_, v_tail_936_, v___x_951_, v___x_952_, v_init_929_);
return v___x_953_;
}
}
else
{
size_t v___x_954_; size_t v___x_955_; lean_object* v___x_956_; 
v___x_954_ = lean_usize_of_nat(v___x_945_);
lean_dec(v___x_945_);
v___x_955_ = lean_usize_of_nat(v___x_946_);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_926_, v_f_928_, v_tail_936_, v___x_954_, v___x_955_, v_init_929_);
return v___x_956_;
}
}
}
}
else
{
lean_object* v_root_957_; lean_object* v_tail_958_; lean_object* v___f_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
lean_inc(v_toBind_932_);
v_root_957_ = lean_ctor_get(v_t_927_, 0);
lean_inc_ref(v_root_957_);
v_tail_958_ = lean_ctor_get(v_t_927_, 1);
lean_inc_ref(v_tail_958_);
lean_dec_ref(v_t_927_);
lean_inc(v_f_928_);
lean_inc_ref(v_inst_926_);
lean_inc_ref(v_toApplicative_931_);
v___f_959_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_959_, 0, v_toApplicative_931_);
lean_closure_set(v___f_959_, 1, v_tail_958_);
lean_closure_set(v___f_959_, 2, v___x_933_);
lean_closure_set(v___f_959_, 3, v_inst_926_);
lean_closure_set(v___f_959_, 4, v_f_928_);
v___x_960_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_926_, v_f_928_, v_root_957_, v_init_929_);
v___x_961_ = lean_apply_4(v_toBind_932_, lean_box(0), lean_box(0), v___x_960_, v___f_959_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___boxed(lean_object* v_inst_962_, lean_object* v_t_963_, lean_object* v_f_964_, lean_object* v_init_965_, lean_object* v_start_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_962_, v_t_963_, v_f_964_, v_init_965_, v_start_966_);
lean_dec(v_start_966_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM(lean_object* v_00_u03b1_968_, lean_object* v_m_969_, lean_object* v_inst_970_, lean_object* v_00_u03b2_971_, lean_object* v_t_972_, lean_object* v_f_973_, lean_object* v_init_974_, lean_object* v_start_975_){
_start:
{
lean_object* v___x_976_; 
v___x_976_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_970_, v_t_972_, v_f_973_, v_init_974_, v_start_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___boxed(lean_object* v_00_u03b1_977_, lean_object* v_m_978_, lean_object* v_inst_979_, lean_object* v_00_u03b2_980_, lean_object* v_t_981_, lean_object* v_f_982_, lean_object* v_init_983_, lean_object* v_start_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lean_PersistentArray_foldlM(v_00_u03b1_977_, v_m_978_, v_inst_979_, v_00_u03b2_980_, v_t_981_, v_f_982_, v_init_983_, v_start_984_);
lean_dec(v_start_984_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(lean_object* v_inst_986_, lean_object* v_f_987_, lean_object* v_x_988_, lean_object* v_x_989_){
_start:
{
if (lean_obj_tag(v_x_988_) == 0)
{
lean_object* v_toApplicative_990_; lean_object* v_cs_991_; lean_object* v_toPure_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_toApplicative_990_ = lean_ctor_get(v_inst_986_, 0);
v_cs_991_ = lean_ctor_get(v_x_988_, 0);
lean_inc_ref(v_cs_991_);
lean_dec_ref_known(v_x_988_, 1);
v_toPure_992_ = lean_ctor_get(v_toApplicative_990_, 1);
v___x_993_ = lean_array_get_size(v_cs_991_);
v___x_994_ = lean_unsigned_to_nat(0u);
v___x_995_ = lean_nat_dec_lt(v___x_994_, v___x_993_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
lean_inc(v_toPure_992_);
lean_dec_ref(v_cs_991_);
lean_dec(v_f_987_);
lean_dec_ref(v_inst_986_);
v___x_996_ = lean_apply_2(v_toPure_992_, lean_box(0), v_x_989_);
return v___x_996_;
}
else
{
lean_object* v___f_997_; size_t v___x_998_; size_t v___x_999_; lean_object* v___x_1000_; 
lean_inc_ref(v_inst_986_);
v___f_997_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_997_, 0, v_inst_986_);
lean_closure_set(v___f_997_, 1, v_f_987_);
v___x_998_ = lean_usize_of_nat(v___x_993_);
v___x_999_ = ((size_t)0ULL);
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_986_, v___f_997_, v_cs_991_, v___x_998_, v___x_999_, v_x_989_);
return v___x_1000_;
}
}
else
{
lean_object* v_toApplicative_1001_; lean_object* v_vs_1002_; lean_object* v_toPure_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v_toApplicative_1001_ = lean_ctor_get(v_inst_986_, 0);
v_vs_1002_ = lean_ctor_get(v_x_988_, 0);
lean_inc_ref(v_vs_1002_);
lean_dec_ref_known(v_x_988_, 1);
v_toPure_1003_ = lean_ctor_get(v_toApplicative_1001_, 1);
v___x_1004_ = lean_array_get_size(v_vs_1002_);
v___x_1005_ = lean_unsigned_to_nat(0u);
v___x_1006_ = lean_nat_dec_lt(v___x_1005_, v___x_1004_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
lean_inc(v_toPure_1003_);
lean_dec_ref(v_vs_1002_);
lean_dec(v_f_987_);
lean_dec_ref(v_inst_986_);
v___x_1007_ = lean_apply_2(v_toPure_1003_, lean_box(0), v_x_989_);
return v___x_1007_;
}
else
{
size_t v___x_1008_; size_t v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_usize_of_nat(v___x_1004_);
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_986_, v_f_987_, v_vs_1002_, v___x_1008_, v___x_1009_, v_x_989_);
return v___x_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0(lean_object* v_inst_1011_, lean_object* v_f_1012_, lean_object* v_c_1013_, lean_object* v_b_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1011_, v_f_1012_, v_c_1013_, v_b_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux(lean_object* v_00_u03b1_1016_, lean_object* v_m_1017_, lean_object* v_00_u03b2_1018_, lean_object* v_inst_1019_, lean_object* v_f_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1019_, v_f_1020_, v_x_1021_, v_x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg___lam__0(lean_object* v_inst_1024_, lean_object* v_f_1025_, lean_object* v_root_1026_, lean_object* v_____do__lift_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1024_, v_f_1025_, v_root_1026_, v_____do__lift_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object* v_inst_1029_, lean_object* v_t_1030_, lean_object* v_f_1031_, lean_object* v_init_1032_){
_start:
{
lean_object* v_toApplicative_1033_; lean_object* v_toBind_1034_; lean_object* v_root_1035_; lean_object* v_tail_1036_; lean_object* v_toPure_1037_; lean_object* v___f_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_toApplicative_1033_ = lean_ctor_get(v_inst_1029_, 0);
v_toBind_1034_ = lean_ctor_get(v_inst_1029_, 1);
lean_inc(v_toBind_1034_);
v_root_1035_ = lean_ctor_get(v_t_1030_, 0);
lean_inc_ref(v_root_1035_);
v_tail_1036_ = lean_ctor_get(v_t_1030_, 1);
lean_inc_ref(v_tail_1036_);
lean_dec_ref(v_t_1030_);
v_toPure_1037_ = lean_ctor_get(v_toApplicative_1033_, 1);
lean_inc(v_f_1031_);
lean_inc_ref(v_inst_1029_);
v___f_1038_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1038_, 0, v_inst_1029_);
lean_closure_set(v___f_1038_, 1, v_f_1031_);
lean_closure_set(v___f_1038_, 2, v_root_1035_);
v___x_1039_ = lean_array_get_size(v_tail_1036_);
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = lean_nat_dec_lt(v___x_1040_, v___x_1039_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_inc(v_toPure_1037_);
lean_dec_ref(v_tail_1036_);
lean_dec(v_f_1031_);
lean_dec_ref(v_inst_1029_);
v___x_1042_ = lean_apply_2(v_toPure_1037_, lean_box(0), v_init_1032_);
v___x_1043_ = lean_apply_4(v_toBind_1034_, lean_box(0), lean_box(0), v___x_1042_, v___f_1038_);
return v___x_1043_;
}
else
{
size_t v___x_1044_; size_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1044_ = lean_usize_of_nat(v___x_1039_);
v___x_1045_ = ((size_t)0ULL);
v___x_1046_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1029_, v_f_1031_, v_tail_1036_, v___x_1044_, v___x_1045_, v_init_1032_);
v___x_1047_ = lean_apply_4(v_toBind_1034_, lean_box(0), lean_box(0), v___x_1046_, v___f_1038_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM(lean_object* v_00_u03b1_1048_, lean_object* v_m_1049_, lean_object* v_00_u03b2_1050_, lean_object* v_inst_1051_, lean_object* v_t_1052_, lean_object* v_f_1053_, lean_object* v_init_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_1051_, v_t_1052_, v_f_1053_, v_init_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__0(lean_object* v_toPure_1056_, lean_object* v_____s_1057_){
_start:
{
lean_object* v_fst_1058_; 
v_fst_1058_ = lean_ctor_get(v_____s_1057_, 0);
if (lean_obj_tag(v_fst_1058_) == 0)
{
lean_object* v_snd_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v_snd_1059_ = lean_ctor_get(v_____s_1057_, 1);
lean_inc(v_snd_1059_);
lean_dec_ref(v_____s_1057_);
v___x_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1060_, 0, v_snd_1059_);
v___x_1061_ = lean_apply_2(v_toPure_1056_, lean_box(0), v___x_1060_);
return v___x_1061_;
}
else
{
lean_object* v_val_1062_; lean_object* v___x_1063_; 
lean_inc_ref(v_fst_1058_);
lean_dec_ref(v_____s_1057_);
v_val_1062_ = lean_ctor_get(v_fst_1058_, 0);
lean_inc(v_val_1062_);
lean_dec_ref_known(v_fst_1058_, 1);
v___x_1063_ = lean_apply_2(v_toPure_1056_, lean_box(0), v_val_1062_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__1(lean_object* v_snd_1064_, lean_object* v_toPure_1065_, lean_object* v___x_1066_, lean_object* v_____do__lift_1067_){
_start:
{
if (lean_obj_tag(v_____do__lift_1067_) == 0)
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_dec(v___x_1066_);
v___x_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1068_, 0, v_____do__lift_1067_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v_snd_1064_);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
v___x_1071_ = lean_apply_2(v_toPure_1065_, lean_box(0), v___x_1070_);
return v___x_1071_;
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1081_; 
lean_dec(v_snd_1064_);
v_a_1072_ = lean_ctor_get(v_____do__lift_1067_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_____do__lift_1067_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1074_ = v_____do__lift_1067_;
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v_____do__lift_1067_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1081_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1066_);
lean_ctor_set(v___x_1076_, 1, v_a_1072_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 0, v___x_1076_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_apply_2(v_toPure_1065_, lean_box(0), v___x_1078_);
return v___x_1079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__5(lean_object* v_toPure_1082_, lean_object* v___x_1083_, lean_object* v_f_1084_, lean_object* v_toBind_1085_, lean_object* v_a_1086_, lean_object* v_x_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_snd_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_snd_1089_ = lean_ctor_get(v___y_1088_, 1);
lean_inc_n(v_snd_1089_, 2);
lean_dec_ref(v___y_1088_);
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1090_, 0, v_snd_1089_);
lean_closure_set(v___f_1090_, 1, v_toPure_1082_);
lean_closure_set(v___f_1090_, 2, v___x_1083_);
v___x_1091_ = lean_apply_2(v_f_1084_, v_a_1086_, v_snd_1089_);
v___x_1092_ = lean_apply_4(v_toBind_1085_, lean_box(0), lean_box(0), v___x_1091_, v___f_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed(lean_object* v_toPure_1093_, lean_object* v___x_1094_, lean_object* v_inst_1095_, lean_object* v_f_1096_, lean_object* v_toBind_1097_, lean_object* v_a_1098_, lean_object* v_x_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lean_PersistentArray_forInAux___redArg___lam__2(v_toPure_1093_, v___x_1094_, v_inst_1095_, v_f_1096_, v_toBind_1097_, v_a_1098_, v_x_1099_, v___y_1100_);
lean_dec_ref(v_a_1098_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg(lean_object* v_inst_1102_, lean_object* v_f_1103_, lean_object* v_n_1104_, lean_object* v_b_1105_){
_start:
{
if (lean_obj_tag(v_n_1104_) == 0)
{
lean_object* v_toApplicative_1106_; lean_object* v_toBind_1107_; lean_object* v_toPure_1108_; lean_object* v_cs_1109_; lean_object* v___f_1110_; lean_object* v___x_1111_; lean_object* v___f_1112_; lean_object* v___x_1113_; size_t v_sz_1114_; size_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_toApplicative_1106_ = lean_ctor_get(v_inst_1102_, 0);
v_toBind_1107_ = lean_ctor_get(v_inst_1102_, 1);
lean_inc_n(v_toBind_1107_, 2);
v_toPure_1108_ = lean_ctor_get(v_toApplicative_1106_, 1);
v_cs_1109_ = lean_ctor_get(v_n_1104_, 0);
lean_inc_n(v_toPure_1108_, 2);
v___f_1110_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1110_, 0, v_toPure_1108_);
v___x_1111_ = lean_box(0);
lean_inc_ref(v_inst_1102_);
v___f_1112_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1112_, 0, v_toPure_1108_);
lean_closure_set(v___f_1112_, 1, v___x_1111_);
lean_closure_set(v___f_1112_, 2, v_inst_1102_);
lean_closure_set(v___f_1112_, 3, v_f_1103_);
lean_closure_set(v___f_1112_, 4, v_toBind_1107_);
v___x_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v_b_1105_);
v_sz_1114_ = lean_array_size(v_cs_1109_);
v___x_1115_ = ((size_t)0ULL);
lean_inc_ref(v_cs_1109_);
v___x_1116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1102_, v_cs_1109_, v___f_1112_, v_sz_1114_, v___x_1115_, v___x_1113_);
v___x_1117_ = lean_apply_4(v_toBind_1107_, lean_box(0), lean_box(0), v___x_1116_, v___f_1110_);
return v___x_1117_;
}
else
{
lean_object* v_toApplicative_1118_; lean_object* v_toBind_1119_; lean_object* v_toPure_1120_; lean_object* v_vs_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; lean_object* v___f_1124_; lean_object* v___x_1125_; size_t v_sz_1126_; size_t v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_toApplicative_1118_ = lean_ctor_get(v_inst_1102_, 0);
v_toBind_1119_ = lean_ctor_get(v_inst_1102_, 1);
lean_inc_n(v_toBind_1119_, 2);
v_toPure_1120_ = lean_ctor_get(v_toApplicative_1118_, 1);
v_vs_1121_ = lean_ctor_get(v_n_1104_, 0);
lean_inc_n(v_toPure_1120_, 2);
v___f_1122_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1122_, 0, v_toPure_1120_);
v___x_1123_ = lean_box(0);
v___f_1124_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__5), 7, 4);
lean_closure_set(v___f_1124_, 0, v_toPure_1120_);
lean_closure_set(v___f_1124_, 1, v___x_1123_);
lean_closure_set(v___f_1124_, 2, v_f_1103_);
lean_closure_set(v___f_1124_, 3, v_toBind_1119_);
v___x_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v_b_1105_);
v_sz_1126_ = lean_array_size(v_vs_1121_);
v___x_1127_ = ((size_t)0ULL);
lean_inc_ref(v_vs_1121_);
v___x_1128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1102_, v_vs_1121_, v___f_1124_, v_sz_1126_, v___x_1127_, v___x_1125_);
v___x_1129_ = lean_apply_4(v_toBind_1119_, lean_box(0), lean_box(0), v___x_1128_, v___f_1122_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2(lean_object* v_toPure_1130_, lean_object* v___x_1131_, lean_object* v_inst_1132_, lean_object* v_f_1133_, lean_object* v_toBind_1134_, lean_object* v_a_1135_, lean_object* v_x_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v_snd_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v_snd_1138_ = lean_ctor_get(v___y_1137_, 1);
lean_inc_n(v_snd_1138_, 2);
lean_dec_ref(v___y_1137_);
v___f_1139_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1139_, 0, v_snd_1138_);
lean_closure_set(v___f_1139_, 1, v_toPure_1130_);
lean_closure_set(v___f_1139_, 2, v___x_1131_);
v___x_1140_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1132_, v_f_1133_, v_a_1135_, v_snd_1138_);
v___x_1141_ = lean_apply_4(v_toBind_1134_, lean_box(0), lean_box(0), v___x_1140_, v___f_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___boxed(lean_object* v_inst_1142_, lean_object* v_f_1143_, lean_object* v_n_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1142_, v_f_1143_, v_n_1144_, v_b_1145_);
lean_dec_ref(v_n_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux(lean_object* v_00_u03b1_1147_, lean_object* v_00_u03b2_1148_, lean_object* v_m_1149_, lean_object* v_inst_1150_, lean_object* v_inh_1151_, lean_object* v_f_1152_, lean_object* v_n_1153_, lean_object* v_b_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1150_, v_f_1152_, v_n_1153_, v_b_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___boxed(lean_object* v_00_u03b1_1156_, lean_object* v_00_u03b2_1157_, lean_object* v_m_1158_, lean_object* v_inst_1159_, lean_object* v_inh_1160_, lean_object* v_f_1161_, lean_object* v_n_1162_, lean_object* v_b_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_PersistentArray_forInAux(v_00_u03b1_1156_, v_00_u03b2_1157_, v_m_1158_, v_inst_1159_, v_inh_1160_, v_f_1161_, v_n_1162_, v_b_1163_);
lean_dec_ref(v_n_1162_);
lean_dec(v_inh_1160_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__0(lean_object* v_toPure_1165_, lean_object* v_____s_1166_){
_start:
{
lean_object* v_fst_1167_; 
v_fst_1167_ = lean_ctor_get(v_____s_1166_, 0);
if (lean_obj_tag(v_fst_1167_) == 0)
{
lean_object* v_snd_1168_; lean_object* v___x_1169_; 
v_snd_1168_ = lean_ctor_get(v_____s_1166_, 1);
lean_inc(v_snd_1168_);
lean_dec_ref(v_____s_1166_);
v___x_1169_ = lean_apply_2(v_toPure_1165_, lean_box(0), v_snd_1168_);
return v___x_1169_;
}
else
{
lean_object* v_val_1170_; lean_object* v___x_1171_; 
lean_inc_ref(v_fst_1167_);
lean_dec_ref(v_____s_1166_);
v_val_1170_ = lean_ctor_get(v_fst_1167_, 0);
lean_inc(v_val_1170_);
lean_dec_ref_known(v_fst_1167_, 1);
v___x_1171_ = lean_apply_2(v_toPure_1165_, lean_box(0), v_val_1170_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__1(lean_object* v_snd_1172_, lean_object* v_toPure_1173_, lean_object* v___x_1174_, lean_object* v_____do__lift_1175_){
_start:
{
if (lean_obj_tag(v_____do__lift_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1186_; 
lean_dec(v___x_1174_);
v_a_1176_ = lean_ctor_get(v_____do__lift_1175_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_____do__lift_1175_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1178_ = v_____do__lift_1175_;
v_isShared_1179_ = v_isSharedCheck_1186_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v_____do__lift_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1186_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v_a_1176_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v_snd_1172_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1181_);
v___x_1183_ = v___x_1178_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_apply_2(v_toPure_1173_, lean_box(0), v___x_1183_);
return v___x_1184_;
}
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v_snd_1172_);
v_a_1187_ = lean_ctor_get(v_____do__lift_1175_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_____do__lift_1175_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1189_ = v_____do__lift_1175_;
v_isShared_1190_ = v_isSharedCheck_1196_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v_____do__lift_1175_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1196_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1174_);
lean_ctor_set(v___x_1191_, 1, v_a_1187_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1191_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_apply_2(v_toPure_1173_, lean_box(0), v___x_1193_);
return v___x_1194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__2(lean_object* v_toPure_1197_, lean_object* v___x_1198_, lean_object* v_f_1199_, lean_object* v_toBind_1200_, lean_object* v_a_1201_, lean_object* v_x_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_snd_1204_; lean_object* v___f_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v_snd_1204_ = lean_ctor_get(v___y_1203_, 1);
lean_inc_n(v_snd_1204_, 2);
lean_dec_ref(v___y_1203_);
v___f_1205_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1205_, 0, v_snd_1204_);
lean_closure_set(v___f_1205_, 1, v_toPure_1197_);
lean_closure_set(v___f_1205_, 2, v___x_1198_);
v___x_1206_ = lean_apply_2(v_f_1199_, v_a_1201_, v_snd_1204_);
v___x_1207_ = lean_apply_4(v_toBind_1200_, lean_box(0), lean_box(0), v___x_1206_, v___f_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__3(lean_object* v_toPure_1208_, lean_object* v_f_1209_, lean_object* v_toBind_1210_, lean_object* v_tail_1211_, lean_object* v_inst_1212_, lean_object* v___f_1213_, lean_object* v_____do__lift_1214_){
_start:
{
if (lean_obj_tag(v_____do__lift_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1216_; 
lean_dec(v___f_1213_);
lean_dec_ref(v_inst_1212_);
lean_dec_ref(v_tail_1211_);
lean_dec(v_toBind_1210_);
lean_dec(v_f_1209_);
v_a_1215_ = lean_ctor_get(v_____do__lift_1214_, 0);
lean_inc(v_a_1215_);
lean_dec_ref_known(v_____do__lift_1214_, 1);
v___x_1216_ = lean_apply_2(v_toPure_1208_, lean_box(0), v_a_1215_);
return v___x_1216_;
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; size_t v_sz_1221_; size_t v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_a_1217_ = lean_ctor_get(v_____do__lift_1214_, 0);
lean_inc(v_a_1217_);
lean_dec_ref_known(v_____do__lift_1214_, 1);
v___x_1218_ = lean_box(0);
lean_inc(v_toBind_1210_);
v___f_1219_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__2), 7, 4);
lean_closure_set(v___f_1219_, 0, v_toPure_1208_);
lean_closure_set(v___f_1219_, 1, v___x_1218_);
lean_closure_set(v___f_1219_, 2, v_f_1209_);
lean_closure_set(v___f_1219_, 3, v_toBind_1210_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1218_);
lean_ctor_set(v___x_1220_, 1, v_a_1217_);
v_sz_1221_ = lean_array_size(v_tail_1211_);
v___x_1222_ = ((size_t)0ULL);
v___x_1223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1212_, v_tail_1211_, v___f_1219_, v_sz_1221_, v___x_1222_, v___x_1220_);
v___x_1224_ = lean_apply_4(v_toBind_1210_, lean_box(0), lean_box(0), v___x_1223_, v___f_1213_);
return v___x_1224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object* v_inst_1225_, lean_object* v_t_1226_, lean_object* v_init_1227_, lean_object* v_f_1228_){
_start:
{
lean_object* v_toApplicative_1229_; lean_object* v_toBind_1230_; lean_object* v_root_1231_; lean_object* v_tail_1232_; lean_object* v_toPure_1233_; lean_object* v___x_1234_; lean_object* v___f_1235_; lean_object* v___f_1236_; lean_object* v___x_1237_; 
v_toApplicative_1229_ = lean_ctor_get(v_inst_1225_, 0);
v_toBind_1230_ = lean_ctor_get(v_inst_1225_, 1);
lean_inc_n(v_toBind_1230_, 2);
v_root_1231_ = lean_ctor_get(v_t_1226_, 0);
v_tail_1232_ = lean_ctor_get(v_t_1226_, 1);
v_toPure_1233_ = lean_ctor_get(v_toApplicative_1229_, 1);
lean_inc_n(v_toPure_1233_, 2);
lean_inc(v_f_1228_);
lean_inc_ref(v_inst_1225_);
v___x_1234_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1225_, v_f_1228_, v_root_1231_, v_init_1227_);
v___f_1235_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1235_, 0, v_toPure_1233_);
lean_inc_ref(v_tail_1232_);
v___f_1236_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1236_, 0, v_toPure_1233_);
lean_closure_set(v___f_1236_, 1, v_f_1228_);
lean_closure_set(v___f_1236_, 2, v_toBind_1230_);
lean_closure_set(v___f_1236_, 3, v_tail_1232_);
lean_closure_set(v___f_1236_, 4, v_inst_1225_);
lean_closure_set(v___f_1236_, 5, v___f_1235_);
v___x_1237_ = lean_apply_4(v_toBind_1230_, lean_box(0), lean_box(0), v___x_1234_, v___f_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___boxed(lean_object* v_inst_1238_, lean_object* v_t_1239_, lean_object* v_init_1240_, lean_object* v_f_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1238_, v_t_1239_, v_init_1240_, v_f_1241_);
lean_dec_ref(v_t_1239_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn(lean_object* v_00_u03b1_1243_, lean_object* v_m_1244_, lean_object* v_inst_1245_, lean_object* v_00_u03b2_1246_, lean_object* v_t_1247_, lean_object* v_init_1248_, lean_object* v_f_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1245_, v_t_1247_, v_init_1248_, v_f_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___boxed(lean_object* v_00_u03b1_1251_, lean_object* v_m_1252_, lean_object* v_inst_1253_, lean_object* v_00_u03b2_1254_, lean_object* v_t_1255_, lean_object* v_init_1256_, lean_object* v_f_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_PersistentArray_forIn(v_00_u03b1_1251_, v_m_1252_, v_inst_1253_, v_00_u03b2_1254_, v_t_1255_, v_init_1256_, v_f_1257_);
lean_dec_ref(v_t_1255_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad___redArg(lean_object* v_inst_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1260_, 0, lean_box(0));
lean_closure_set(v___x_1260_, 1, lean_box(0));
lean_closure_set(v___x_1260_, 2, v_inst_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad(lean_object* v_00_u03b1_1261_, lean_object* v_m_1262_, lean_object* v_inst_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1264_, 0, lean_box(0));
lean_closure_set(v___x_1264_, 1, lean_box(0));
lean_closure_set(v___x_1264_, 2, v_inst_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(lean_object* v_toPure_1265_, lean_object* v_____s_1266_){
_start:
{
lean_object* v_fst_1267_; 
v_fst_1267_ = lean_ctor_get(v_____s_1266_, 0);
lean_inc(v_fst_1267_);
lean_dec_ref(v_____s_1266_);
if (lean_obj_tag(v_fst_1267_) == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_apply_2(v_toPure_1265_, lean_box(0), v___x_1268_);
return v___x_1269_;
}
else
{
lean_object* v_val_1270_; lean_object* v___x_1271_; 
v_val_1270_ = lean_ctor_get(v_fst_1267_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v_fst_1267_, 1);
v___x_1271_ = lean_apply_2(v_toPure_1265_, lean_box(0), v_val_1270_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(lean_object* v___x_1272_, lean_object* v_toPure_1273_, lean_object* v___x_1274_, lean_object* v_____do__lift_1275_){
_start:
{
if (lean_obj_tag(v_____do__lift_1275_) == 1)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
lean_dec_ref(v___x_1274_);
v___x_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1276_, 0, v_____do__lift_1275_);
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v___x_1272_);
v___x_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
v___x_1279_ = lean_apply_2(v_toPure_1273_, lean_box(0), v___x_1278_);
return v___x_1279_;
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec(v_____do__lift_1275_);
v___x_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1274_);
v___x_1281_ = lean_apply_2(v_toPure_1273_, lean_box(0), v___x_1280_);
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(lean_object* v_f_1282_, lean_object* v_toBind_1283_, lean_object* v___f_1284_, lean_object* v_a_1285_, lean_object* v_x_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_apply_1(v_f_1282_, v_a_1285_);
v___x_1289_ = lean_apply_4(v_toBind_1283_, lean_box(0), lean_box(0), v___x_1288_, v___f_1284_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(lean_object* v_f_1290_, lean_object* v_toBind_1291_, lean_object* v___f_1292_, lean_object* v_a_1293_, lean_object* v_x_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(v_f_1290_, v_toBind_1291_, v___f_1292_, v_a_1293_, v_x_1294_, v___y_1295_);
lean_dec_ref(v___y_1295_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(lean_object* v_inst_1300_, lean_object* v_f_1301_, lean_object* v_toBind_1302_, lean_object* v___f_1303_, lean_object* v_a_1304_, lean_object* v_x_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(v_inst_1300_, v_f_1301_, v_toBind_1302_, v___f_1303_, v_a_1304_, v_x_1305_, v___y_1306_);
lean_dec_ref(v___y_1306_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg(lean_object* v_inst_1308_, lean_object* v_f_1309_, lean_object* v_x_1310_){
_start:
{
if (lean_obj_tag(v_x_1310_) == 0)
{
lean_object* v_toApplicative_1311_; lean_object* v_cs_1312_; lean_object* v_toBind_1313_; lean_object* v_toPure_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___f_1317_; lean_object* v___f_1318_; lean_object* v___f_1319_; size_t v_sz_1320_; size_t v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_toApplicative_1311_ = lean_ctor_get(v_inst_1308_, 0);
v_cs_1312_ = lean_ctor_get(v_x_1310_, 0);
lean_inc_ref(v_cs_1312_);
lean_dec_ref_known(v_x_1310_, 1);
v_toBind_1313_ = lean_ctor_get(v_inst_1308_, 1);
lean_inc_n(v_toBind_1313_, 2);
v_toPure_1314_ = lean_ctor_get(v_toApplicative_1311_, 1);
v___x_1315_ = lean_box(0);
v___x_1316_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1314_, 2);
v___f_1317_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1317_, 0, v_toPure_1314_);
v___f_1318_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1318_, 0, v___x_1315_);
lean_closure_set(v___f_1318_, 1, v_toPure_1314_);
lean_closure_set(v___f_1318_, 2, v___x_1316_);
lean_inc_ref(v_inst_1308_);
v___f_1319_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1319_, 0, v_inst_1308_);
lean_closure_set(v___f_1319_, 1, v_f_1309_);
lean_closure_set(v___f_1319_, 2, v_toBind_1313_);
lean_closure_set(v___f_1319_, 3, v___f_1318_);
v_sz_1320_ = lean_array_size(v_cs_1312_);
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1308_, v_cs_1312_, v___f_1319_, v_sz_1320_, v___x_1321_, v___x_1316_);
v___x_1323_ = lean_apply_4(v_toBind_1313_, lean_box(0), lean_box(0), v___x_1322_, v___f_1317_);
return v___x_1323_;
}
else
{
lean_object* v_toApplicative_1324_; lean_object* v_vs_1325_; lean_object* v_toBind_1326_; lean_object* v_toPure_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___f_1330_; lean_object* v___f_1331_; lean_object* v___f_1332_; size_t v_sz_1333_; size_t v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v_toApplicative_1324_ = lean_ctor_get(v_inst_1308_, 0);
v_vs_1325_ = lean_ctor_get(v_x_1310_, 0);
lean_inc_ref(v_vs_1325_);
lean_dec_ref_known(v_x_1310_, 1);
v_toBind_1326_ = lean_ctor_get(v_inst_1308_, 1);
lean_inc_n(v_toBind_1326_, 2);
v_toPure_1327_ = lean_ctor_get(v_toApplicative_1324_, 1);
v___x_1328_ = lean_box(0);
v___x_1329_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1327_, 2);
v___f_1330_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1330_, 0, v_toPure_1327_);
v___f_1331_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1331_, 0, v___x_1328_);
lean_closure_set(v___f_1331_, 1, v_toPure_1327_);
lean_closure_set(v___f_1331_, 2, v___x_1329_);
v___f_1332_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1332_, 0, v_f_1309_);
lean_closure_set(v___f_1332_, 1, v_toBind_1326_);
lean_closure_set(v___f_1332_, 2, v___f_1331_);
v_sz_1333_ = lean_array_size(v_vs_1325_);
v___x_1334_ = ((size_t)0ULL);
v___x_1335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1308_, v_vs_1325_, v___f_1332_, v_sz_1333_, v___x_1334_, v___x_1329_);
v___x_1336_ = lean_apply_4(v_toBind_1326_, lean_box(0), lean_box(0), v___x_1335_, v___f_1330_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(lean_object* v_inst_1337_, lean_object* v_f_1338_, lean_object* v_toBind_1339_, lean_object* v___f_1340_, lean_object* v_a_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1337_, v_f_1338_, v_a_1341_);
v___x_1345_ = lean_apply_4(v_toBind_1339_, lean_box(0), lean_box(0), v___x_1344_, v___f_1340_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux(lean_object* v_00_u03b1_1346_, lean_object* v_m_1347_, lean_object* v_inst_1348_, lean_object* v_00_u03b2_1349_, lean_object* v_f_1350_, lean_object* v_x_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1348_, v_f_1350_, v_x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(lean_object* v_toPure_1353_, lean_object* v_____do__lift_1354_, lean_object* v_____s_1355_){
_start:
{
lean_object* v_fst_1356_; 
v_fst_1356_ = lean_ctor_get(v_____s_1355_, 0);
lean_inc(v_fst_1356_);
lean_dec_ref(v_____s_1355_);
if (lean_obj_tag(v_fst_1356_) == 0)
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_apply_2(v_toPure_1353_, lean_box(0), v_____do__lift_1354_);
return v___x_1357_;
}
else
{
lean_object* v_val_1358_; lean_object* v___x_1359_; 
lean_dec(v_____do__lift_1354_);
v_val_1358_ = lean_ctor_get(v_fst_1356_, 0);
lean_inc(v_val_1358_);
lean_dec_ref_known(v_fst_1356_, 1);
v___x_1359_ = lean_apply_2(v_toPure_1353_, lean_box(0), v_val_1358_);
return v___x_1359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(lean_object* v___x_1360_, lean_object* v_toPure_1361_, lean_object* v___x_1362_, lean_object* v_____do__lift_1363_){
_start:
{
if (lean_obj_tag(v_____do__lift_1363_) == 1)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
lean_dec_ref(v___x_1362_);
v___x_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_____do__lift_1363_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v___x_1360_);
v___x_1366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
v___x_1367_ = lean_apply_2(v_toPure_1361_, lean_box(0), v___x_1366_);
return v___x_1367_;
}
else
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_dec(v_____do__lift_1363_);
v___x_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1362_);
v___x_1369_ = lean_apply_2(v_toPure_1361_, lean_box(0), v___x_1368_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1370_, lean_object* v_toBind_1371_, lean_object* v___f_1372_, lean_object* v_a_1373_, lean_object* v_x_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = lean_apply_1(v_f_1370_, v_a_1373_);
v___x_1377_ = lean_apply_4(v_toBind_1371_, lean_box(0), lean_box(0), v___x_1376_, v___f_1372_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1378_, lean_object* v_toBind_1379_, lean_object* v___f_1380_, lean_object* v_a_1381_, lean_object* v_x_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(v_f_1378_, v_toBind_1379_, v___f_1380_, v_a_1381_, v_x_1382_, v___y_1383_);
lean_dec_ref(v___y_1383_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(lean_object* v_toPure_1385_, lean_object* v_f_1386_, lean_object* v_toBind_1387_, lean_object* v_tail_1388_, lean_object* v_inst_1389_, lean_object* v_____do__lift_1390_){
_start:
{
if (lean_obj_tag(v_____do__lift_1390_) == 0)
{
lean_object* v___f_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___f_1394_; lean_object* v___f_1395_; size_t v_sz_1396_; size_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_inc(v_toPure_1385_);
v___f_1391_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1391_, 0, v_toPure_1385_);
lean_closure_set(v___f_1391_, 1, v_____do__lift_1390_);
v___x_1392_ = lean_box(0);
v___x_1393_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
v___f_1394_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1394_, 0, v___x_1392_);
lean_closure_set(v___f_1394_, 1, v_toPure_1385_);
lean_closure_set(v___f_1394_, 2, v___x_1393_);
lean_inc(v_toBind_1387_);
v___f_1395_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1395_, 0, v_f_1386_);
lean_closure_set(v___f_1395_, 1, v_toBind_1387_);
lean_closure_set(v___f_1395_, 2, v___f_1394_);
v_sz_1396_ = lean_array_size(v_tail_1388_);
v___x_1397_ = ((size_t)0ULL);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1389_, v_tail_1388_, v___f_1395_, v_sz_1396_, v___x_1397_, v___x_1393_);
v___x_1399_ = lean_apply_4(v_toBind_1387_, lean_box(0), lean_box(0), v___x_1398_, v___f_1391_);
return v___x_1399_;
}
else
{
lean_object* v___x_1400_; 
lean_dec_ref(v_inst_1389_);
lean_dec_ref(v_tail_1388_);
lean_dec(v_toBind_1387_);
lean_dec(v_f_1386_);
v___x_1400_ = lean_apply_2(v_toPure_1385_, lean_box(0), v_____do__lift_1390_);
return v___x_1400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object* v_inst_1401_, lean_object* v_t_1402_, lean_object* v_f_1403_){
_start:
{
lean_object* v_toApplicative_1404_; lean_object* v_toBind_1405_; lean_object* v_root_1406_; lean_object* v_tail_1407_; lean_object* v_toPure_1408_; lean_object* v___x_1409_; lean_object* v___f_1410_; lean_object* v___x_1411_; 
v_toApplicative_1404_ = lean_ctor_get(v_inst_1401_, 0);
v_toBind_1405_ = lean_ctor_get(v_inst_1401_, 1);
lean_inc_n(v_toBind_1405_, 2);
v_root_1406_ = lean_ctor_get(v_t_1402_, 0);
lean_inc_ref(v_root_1406_);
v_tail_1407_ = lean_ctor_get(v_t_1402_, 1);
lean_inc_ref(v_tail_1407_);
lean_dec_ref(v_t_1402_);
v_toPure_1408_ = lean_ctor_get(v_toApplicative_1404_, 1);
lean_inc(v_toPure_1408_);
lean_inc(v_f_1403_);
lean_inc_ref(v_inst_1401_);
v___x_1409_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1401_, v_f_1403_, v_root_1406_);
v___f_1410_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1410_, 0, v_toPure_1408_);
lean_closure_set(v___f_1410_, 1, v_f_1403_);
lean_closure_set(v___f_1410_, 2, v_toBind_1405_);
lean_closure_set(v___f_1410_, 3, v_tail_1407_);
lean_closure_set(v___f_1410_, 4, v_inst_1401_);
v___x_1411_ = lean_apply_4(v_toBind_1405_, lean_box(0), lean_box(0), v___x_1409_, v___f_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f(lean_object* v_00_u03b1_1412_, lean_object* v_m_1413_, lean_object* v_inst_1414_, lean_object* v_00_u03b2_1415_, lean_object* v_t_1416_, lean_object* v_f_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_1414_, v_t_1416_, v_f_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg(lean_object* v_inst_1419_, lean_object* v_f_1420_, lean_object* v_x_1421_){
_start:
{
if (lean_obj_tag(v_x_1421_) == 0)
{
lean_object* v_cs_1422_; lean_object* v___f_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; 
v_cs_1422_ = lean_ctor_get(v_x_1421_, 0);
lean_inc_ref(v_cs_1422_);
lean_dec_ref_known(v_x_1421_, 1);
lean_inc_ref(v_inst_1419_);
v___f_1423_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1423_, 0, v_inst_1419_);
lean_closure_set(v___f_1423_, 1, v_f_1420_);
v___x_1424_ = lean_array_get_size(v_cs_1422_);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1419_, v___f_1423_, v_cs_1422_, v___x_1424_, lean_box(0));
return v___x_1425_;
}
else
{
lean_object* v_vs_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v_vs_1426_ = lean_ctor_get(v_x_1421_, 0);
lean_inc_ref(v_vs_1426_);
lean_dec_ref_known(v_x_1421_, 1);
v___x_1427_ = lean_array_get_size(v_vs_1426_);
v___x_1428_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1419_, v_f_1420_, v_vs_1426_, v___x_1427_, lean_box(0));
return v___x_1428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(lean_object* v_inst_1429_, lean_object* v_f_1430_, lean_object* v_c_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1429_, v_f_1430_, v_c_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux(lean_object* v_00_u03b1_1433_, lean_object* v_m_1434_, lean_object* v_inst_1435_, lean_object* v_00_u03b2_1436_, lean_object* v_f_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1435_, v_f_1437_, v_x_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(lean_object* v_inst_1440_, lean_object* v_f_1441_, lean_object* v_root_1442_, lean_object* v_toPure_1443_, lean_object* v_____do__lift_1444_){
_start:
{
if (lean_obj_tag(v_____do__lift_1444_) == 0)
{
lean_object* v___x_1445_; 
lean_dec(v_toPure_1443_);
v___x_1445_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1440_, v_f_1441_, v_root_1442_);
return v___x_1445_;
}
else
{
lean_object* v___x_1446_; 
lean_dec_ref(v_root_1442_);
lean_dec(v_f_1441_);
lean_dec_ref(v_inst_1440_);
v___x_1446_ = lean_apply_2(v_toPure_1443_, lean_box(0), v_____do__lift_1444_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object* v_inst_1447_, lean_object* v_t_1448_, lean_object* v_f_1449_){
_start:
{
lean_object* v_toApplicative_1450_; lean_object* v_toBind_1451_; lean_object* v_root_1452_; lean_object* v_tail_1453_; lean_object* v_toPure_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___f_1457_; lean_object* v___x_1458_; 
v_toApplicative_1450_ = lean_ctor_get(v_inst_1447_, 0);
v_toBind_1451_ = lean_ctor_get(v_inst_1447_, 1);
lean_inc(v_toBind_1451_);
v_root_1452_ = lean_ctor_get(v_t_1448_, 0);
lean_inc_ref(v_root_1452_);
v_tail_1453_ = lean_ctor_get(v_t_1448_, 1);
lean_inc_ref(v_tail_1453_);
lean_dec_ref(v_t_1448_);
v_toPure_1454_ = lean_ctor_get(v_toApplicative_1450_, 1);
lean_inc(v_toPure_1454_);
v___x_1455_ = lean_array_get_size(v_tail_1453_);
lean_inc(v_f_1449_);
lean_inc_ref(v_inst_1447_);
v___x_1456_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1447_, v_f_1449_, v_tail_1453_, v___x_1455_, lean_box(0));
v___f_1457_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1457_, 0, v_inst_1447_);
lean_closure_set(v___f_1457_, 1, v_f_1449_);
lean_closure_set(v___f_1457_, 2, v_root_1452_);
lean_closure_set(v___f_1457_, 3, v_toPure_1454_);
v___x_1458_ = lean_apply_4(v_toBind_1451_, lean_box(0), lean_box(0), v___x_1456_, v___f_1457_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f(lean_object* v_00_u03b1_1459_, lean_object* v_m_1460_, lean_object* v_inst_1461_, lean_object* v_00_u03b2_1462_, lean_object* v_t_1463_, lean_object* v_f_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_1461_, v_t_1463_, v_f_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__1(lean_object* v_f_1466_, lean_object* v_x_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_apply_1(v_f_1466_, v___y_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg(lean_object* v_inst_1470_, lean_object* v_f_1471_, lean_object* v_x_1472_){
_start:
{
if (lean_obj_tag(v_x_1472_) == 0)
{
lean_object* v_toApplicative_1473_; lean_object* v_cs_1474_; lean_object* v_toPure_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_toApplicative_1473_ = lean_ctor_get(v_inst_1470_, 0);
v_cs_1474_ = lean_ctor_get(v_x_1472_, 0);
lean_inc_ref(v_cs_1474_);
lean_dec_ref_known(v_x_1472_, 1);
v_toPure_1475_ = lean_ctor_get(v_toApplicative_1473_, 1);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_array_get_size(v_cs_1474_);
v___x_1478_ = lean_box(0);
v___x_1479_ = lean_nat_dec_lt(v___x_1476_, v___x_1477_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; 
lean_inc(v_toPure_1475_);
lean_dec_ref(v_cs_1474_);
lean_dec(v_f_1471_);
lean_dec_ref(v_inst_1470_);
v___x_1480_ = lean_apply_2(v_toPure_1475_, lean_box(0), v___x_1478_);
return v___x_1480_;
}
else
{
lean_object* v___f_1481_; uint8_t v___x_1482_; 
lean_inc_ref(v_inst_1470_);
v___f_1481_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1481_, 0, v_inst_1470_);
lean_closure_set(v___f_1481_, 1, v_f_1471_);
v___x_1482_ = lean_nat_dec_le(v___x_1477_, v___x_1477_);
if (v___x_1482_ == 0)
{
if (v___x_1479_ == 0)
{
lean_object* v___x_1483_; 
lean_inc(v_toPure_1475_);
lean_dec_ref(v___f_1481_);
lean_dec_ref(v_cs_1474_);
lean_dec_ref(v_inst_1470_);
v___x_1483_ = lean_apply_2(v_toPure_1475_, lean_box(0), v___x_1478_);
return v___x_1483_;
}
else
{
size_t v___x_1484_; size_t v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = ((size_t)0ULL);
v___x_1485_ = lean_usize_of_nat(v___x_1477_);
v___x_1486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1470_, v___f_1481_, v_cs_1474_, v___x_1484_, v___x_1485_, v___x_1478_);
return v___x_1486_;
}
}
else
{
size_t v___x_1487_; size_t v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = lean_usize_of_nat(v___x_1477_);
v___x_1489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1470_, v___f_1481_, v_cs_1474_, v___x_1487_, v___x_1488_, v___x_1478_);
return v___x_1489_;
}
}
}
else
{
lean_object* v_toApplicative_1490_; lean_object* v_vs_1491_; lean_object* v_toPure_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v_toApplicative_1490_ = lean_ctor_get(v_inst_1470_, 0);
v_vs_1491_ = lean_ctor_get(v_x_1472_, 0);
lean_inc_ref(v_vs_1491_);
lean_dec_ref_known(v_x_1472_, 1);
v_toPure_1492_ = lean_ctor_get(v_toApplicative_1490_, 1);
v___x_1493_ = lean_unsigned_to_nat(0u);
v___x_1494_ = lean_array_get_size(v_vs_1491_);
v___x_1495_ = lean_box(0);
v___x_1496_ = lean_nat_dec_lt(v___x_1493_, v___x_1494_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
lean_inc(v_toPure_1492_);
lean_dec_ref(v_vs_1491_);
lean_dec(v_f_1471_);
lean_dec_ref(v_inst_1470_);
v___x_1497_ = lean_apply_2(v_toPure_1492_, lean_box(0), v___x_1495_);
return v___x_1497_;
}
else
{
lean_object* v___f_1498_; uint8_t v___x_1499_; 
v___f_1498_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1498_, 0, v_f_1471_);
v___x_1499_ = lean_nat_dec_le(v___x_1494_, v___x_1494_);
if (v___x_1499_ == 0)
{
if (v___x_1496_ == 0)
{
lean_object* v___x_1500_; 
lean_inc(v_toPure_1492_);
lean_dec_ref(v___f_1498_);
lean_dec_ref(v_vs_1491_);
lean_dec_ref(v_inst_1470_);
v___x_1500_ = lean_apply_2(v_toPure_1492_, lean_box(0), v___x_1495_);
return v___x_1500_;
}
else
{
size_t v___x_1501_; size_t v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = ((size_t)0ULL);
v___x_1502_ = lean_usize_of_nat(v___x_1494_);
v___x_1503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1470_, v___f_1498_, v_vs_1491_, v___x_1501_, v___x_1502_, v___x_1495_);
return v___x_1503_;
}
}
else
{
size_t v___x_1504_; size_t v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = ((size_t)0ULL);
v___x_1505_ = lean_usize_of_nat(v___x_1494_);
v___x_1506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1470_, v___f_1498_, v_vs_1491_, v___x_1504_, v___x_1505_, v___x_1495_);
return v___x_1506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__0(lean_object* v_inst_1507_, lean_object* v_f_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1507_, v_f_1508_, v___y_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux(lean_object* v_00_u03b1_1512_, lean_object* v_m_1513_, lean_object* v_inst_1514_, lean_object* v_f_1515_, lean_object* v_x_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1514_, v_f_1515_, v_x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__0(lean_object* v_f_1518_, lean_object* v_x_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_apply_1(v_f_1518_, v___y_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__1(lean_object* v_tail_1522_, lean_object* v_toPure_1523_, lean_object* v_inst_1524_, lean_object* v___f_1525_, lean_object* v_x_1526_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = lean_array_get_size(v_tail_1522_);
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_nat_dec_lt(v___x_1527_, v___x_1528_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; 
lean_dec(v___f_1525_);
lean_dec_ref(v_inst_1524_);
lean_dec_ref(v_tail_1522_);
v___x_1531_ = lean_apply_2(v_toPure_1523_, lean_box(0), v___x_1529_);
return v___x_1531_;
}
else
{
uint8_t v___x_1532_; 
v___x_1532_ = lean_nat_dec_le(v___x_1528_, v___x_1528_);
if (v___x_1532_ == 0)
{
if (v___x_1530_ == 0)
{
lean_object* v___x_1533_; 
lean_dec(v___f_1525_);
lean_dec_ref(v_inst_1524_);
lean_dec_ref(v_tail_1522_);
v___x_1533_ = lean_apply_2(v_toPure_1523_, lean_box(0), v___x_1529_);
return v___x_1533_;
}
else
{
size_t v___x_1534_; size_t v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_toPure_1523_);
v___x_1534_ = ((size_t)0ULL);
v___x_1535_ = lean_usize_of_nat(v___x_1528_);
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1524_, v___f_1525_, v_tail_1522_, v___x_1534_, v___x_1535_, v___x_1529_);
return v___x_1536_;
}
}
else
{
size_t v___x_1537_; size_t v___x_1538_; lean_object* v___x_1539_; 
lean_dec(v_toPure_1523_);
v___x_1537_ = ((size_t)0ULL);
v___x_1538_ = lean_usize_of_nat(v___x_1528_);
v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1524_, v___f_1525_, v_tail_1522_, v___x_1537_, v___x_1538_, v___x_1529_);
return v___x_1539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg(lean_object* v_inst_1540_, lean_object* v_t_1541_, lean_object* v_f_1542_){
_start:
{
lean_object* v_toApplicative_1543_; lean_object* v_toPure_1544_; lean_object* v_toSeqRight_1545_; lean_object* v_root_1546_; lean_object* v_tail_1547_; lean_object* v___f_1548_; lean_object* v___f_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v_toApplicative_1543_ = lean_ctor_get(v_inst_1540_, 0);
v_toPure_1544_ = lean_ctor_get(v_toApplicative_1543_, 1);
v_toSeqRight_1545_ = lean_ctor_get(v_toApplicative_1543_, 4);
lean_inc(v_toSeqRight_1545_);
v_root_1546_ = lean_ctor_get(v_t_1541_, 0);
lean_inc_ref(v_root_1546_);
v_tail_1547_ = lean_ctor_get(v_t_1541_, 1);
lean_inc_ref(v_tail_1547_);
lean_dec_ref(v_t_1541_);
lean_inc(v_f_1542_);
v___f_1548_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1548_, 0, v_f_1542_);
lean_inc_ref(v_inst_1540_);
lean_inc(v_toPure_1544_);
v___f_1549_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1549_, 0, v_tail_1547_);
lean_closure_set(v___f_1549_, 1, v_toPure_1544_);
lean_closure_set(v___f_1549_, 2, v_inst_1540_);
lean_closure_set(v___f_1549_, 3, v___f_1548_);
v___x_1550_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1540_, v_f_1542_, v_root_1546_);
v___x_1551_ = lean_apply_4(v_toSeqRight_1545_, lean_box(0), lean_box(0), v___x_1550_, v___f_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0(lean_object* v_00_u03b1_1552_, lean_object* v_m_1553_, lean_object* v_inst_1554_, lean_object* v_t_1555_, lean_object* v_f_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1554_, v_t_1555_, v_f_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(lean_object* v_toApplicative_1558_, lean_object* v_j_1559_, lean_object* v_cs_1560_, lean_object* v_inst_1561_, lean_object* v___f_1562_, lean_object* v_____r_1563_){
_start:
{
lean_object* v_toPure_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; 
v_toPure_1564_ = lean_ctor_get(v_toApplicative_1558_, 1);
lean_inc(v_toPure_1564_);
lean_dec_ref(v_toApplicative_1558_);
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_nat_add(v_j_1559_, v___x_1565_);
v___x_1567_ = lean_array_get_size(v_cs_1560_);
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_nat_dec_lt(v___x_1566_, v___x_1567_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; 
lean_dec(v___x_1566_);
lean_dec(v___f_1562_);
lean_dec_ref(v_inst_1561_);
lean_dec_ref(v_cs_1560_);
v___x_1570_ = lean_apply_2(v_toPure_1564_, lean_box(0), v___x_1568_);
return v___x_1570_;
}
else
{
uint8_t v___x_1571_; 
v___x_1571_ = lean_nat_dec_le(v___x_1567_, v___x_1567_);
if (v___x_1571_ == 0)
{
if (v___x_1569_ == 0)
{
lean_object* v___x_1572_; 
lean_dec(v___x_1566_);
lean_dec(v___f_1562_);
lean_dec_ref(v_inst_1561_);
lean_dec_ref(v_cs_1560_);
v___x_1572_ = lean_apply_2(v_toPure_1564_, lean_box(0), v___x_1568_);
return v___x_1572_;
}
else
{
size_t v___x_1573_; size_t v___x_1574_; lean_object* v___x_1575_; 
lean_dec(v_toPure_1564_);
v___x_1573_ = lean_usize_of_nat(v___x_1566_);
lean_dec(v___x_1566_);
v___x_1574_ = lean_usize_of_nat(v___x_1567_);
v___x_1575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1561_, v___f_1562_, v_cs_1560_, v___x_1573_, v___x_1574_, v___x_1568_);
return v___x_1575_;
}
}
else
{
size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
lean_dec(v_toPure_1564_);
v___x_1576_ = lean_usize_of_nat(v___x_1566_);
lean_dec(v___x_1566_);
v___x_1577_ = lean_usize_of_nat(v___x_1567_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1561_, v___f_1562_, v_cs_1560_, v___x_1576_, v___x_1577_, v___x_1568_);
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_1579_, lean_object* v_j_1580_, lean_object* v_cs_1581_, lean_object* v_inst_1582_, lean_object* v___f_1583_, lean_object* v_____r_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(v_toApplicative_1579_, v_j_1580_, v_cs_1581_, v_inst_1582_, v___f_1583_, v_____r_1584_);
lean_dec(v_j_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(lean_object* v_inst_1586_, lean_object* v_f_1587_, lean_object* v_x_1588_, size_t v_x_1589_, size_t v_x_1590_){
_start:
{
if (lean_obj_tag(v_x_1588_) == 0)
{
lean_object* v_toApplicative_1591_; lean_object* v_toBind_1592_; lean_object* v_cs_1593_; lean_object* v___f_1594_; lean_object* v___x_1595_; size_t v___x_1596_; lean_object* v_j_1597_; lean_object* v___f_1598_; lean_object* v___x_1599_; size_t v___x_1600_; size_t v___x_1601_; size_t v___x_1602_; size_t v___x_1603_; size_t v___x_1604_; size_t v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v_toApplicative_1591_ = lean_ctor_get(v_inst_1586_, 0);
v_toBind_1592_ = lean_ctor_get(v_inst_1586_, 1);
lean_inc(v_toBind_1592_);
v_cs_1593_ = lean_ctor_get(v_x_1588_, 0);
lean_inc_ref_n(v_cs_1593_, 2);
lean_dec_ref_known(v_x_1588_, 1);
lean_inc(v_f_1587_);
lean_inc_ref_n(v_inst_1586_, 2);
v___f_1594_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1594_, 0, v_inst_1586_);
lean_closure_set(v___f_1594_, 1, v_f_1587_);
v___x_1595_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_1596_ = lean_usize_shift_right(v_x_1589_, v_x_1590_);
v_j_1597_ = lean_usize_to_nat(v___x_1596_);
lean_inc(v_j_1597_);
lean_inc_ref(v_toApplicative_1591_);
v___f_1598_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1598_, 0, v_toApplicative_1591_);
lean_closure_set(v___f_1598_, 1, v_j_1597_);
lean_closure_set(v___f_1598_, 2, v_cs_1593_);
lean_closure_set(v___f_1598_, 3, v_inst_1586_);
lean_closure_set(v___f_1598_, 4, v___f_1594_);
v___x_1599_ = lean_array_get(v___x_1595_, v_cs_1593_, v_j_1597_);
lean_dec(v_j_1597_);
lean_dec_ref(v_cs_1593_);
v___x_1600_ = ((size_t)1ULL);
v___x_1601_ = lean_usize_shift_left(v___x_1600_, v_x_1590_);
v___x_1602_ = lean_usize_sub(v___x_1601_, v___x_1600_);
v___x_1603_ = lean_usize_land(v_x_1589_, v___x_1602_);
v___x_1604_ = ((size_t)5ULL);
v___x_1605_ = lean_usize_sub(v_x_1590_, v___x_1604_);
v___x_1606_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1586_, v_f_1587_, v___x_1599_, v___x_1603_, v___x_1605_);
v___x_1607_ = lean_apply_4(v_toBind_1592_, lean_box(0), lean_box(0), v___x_1606_, v___f_1598_);
return v___x_1607_;
}
else
{
lean_object* v_toApplicative_1608_; lean_object* v_vs_1609_; lean_object* v_toPure_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_toApplicative_1608_ = lean_ctor_get(v_inst_1586_, 0);
v_vs_1609_ = lean_ctor_get(v_x_1588_, 0);
lean_inc_ref(v_vs_1609_);
lean_dec_ref_known(v_x_1588_, 1);
v_toPure_1610_ = lean_ctor_get(v_toApplicative_1608_, 1);
v___x_1611_ = lean_usize_to_nat(v_x_1589_);
v___x_1612_ = lean_array_get_size(v_vs_1609_);
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_nat_dec_lt(v___x_1611_, v___x_1612_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; 
lean_inc(v_toPure_1610_);
lean_dec(v___x_1611_);
lean_dec_ref(v_vs_1609_);
lean_dec(v_f_1587_);
lean_dec_ref(v_inst_1586_);
v___x_1615_ = lean_apply_2(v_toPure_1610_, lean_box(0), v___x_1613_);
return v___x_1615_;
}
else
{
lean_object* v___f_1616_; uint8_t v___x_1617_; 
v___f_1616_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1616_, 0, v_f_1587_);
v___x_1617_ = lean_nat_dec_le(v___x_1612_, v___x_1612_);
if (v___x_1617_ == 0)
{
if (v___x_1614_ == 0)
{
lean_object* v___x_1618_; 
lean_inc(v_toPure_1610_);
lean_dec_ref(v___f_1616_);
lean_dec(v___x_1611_);
lean_dec_ref(v_vs_1609_);
lean_dec_ref(v_inst_1586_);
v___x_1618_ = lean_apply_2(v_toPure_1610_, lean_box(0), v___x_1613_);
return v___x_1618_;
}
else
{
size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; 
v___x_1619_ = lean_usize_of_nat(v___x_1611_);
lean_dec(v___x_1611_);
v___x_1620_ = lean_usize_of_nat(v___x_1612_);
v___x_1621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1586_, v___f_1616_, v_vs_1609_, v___x_1619_, v___x_1620_, v___x_1613_);
return v___x_1621_;
}
}
else
{
size_t v___x_1622_; size_t v___x_1623_; lean_object* v___x_1624_; 
v___x_1622_ = lean_usize_of_nat(v___x_1611_);
lean_dec(v___x_1611_);
v___x_1623_ = lean_usize_of_nat(v___x_1612_);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1586_, v___f_1616_, v_vs_1609_, v___x_1622_, v___x_1623_, v___x_1613_);
return v___x_1624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___boxed(lean_object* v_inst_1625_, lean_object* v_f_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_){
_start:
{
size_t v_x_272__boxed_1630_; size_t v_x_273__boxed_1631_; lean_object* v_res_1632_; 
v_x_272__boxed_1630_ = lean_unbox_usize(v_x_1628_);
lean_dec(v_x_1628_);
v_x_273__boxed_1631_ = lean_unbox_usize(v_x_1629_);
lean_dec(v_x_1629_);
v_res_1632_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1625_, v_f_1626_, v_x_1627_, v_x_272__boxed_1630_, v_x_273__boxed_1631_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(lean_object* v_00_u03b1_1633_, lean_object* v_m_1634_, lean_object* v_inst_1635_, lean_object* v_f_1636_, lean_object* v_x_1637_, size_t v_x_1638_, size_t v_x_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1635_, v_f_1636_, v_x_1637_, v_x_1638_, v_x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___boxed(lean_object* v_00_u03b1_1641_, lean_object* v_m_1642_, lean_object* v_inst_1643_, lean_object* v_f_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_){
_start:
{
size_t v_x_342__boxed_1648_; size_t v_x_343__boxed_1649_; lean_object* v_res_1650_; 
v_x_342__boxed_1648_ = lean_unbox_usize(v_x_1646_);
lean_dec(v_x_1646_);
v_x_343__boxed_1649_ = lean_unbox_usize(v_x_1647_);
lean_dec(v_x_1647_);
v_res_1650_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(v_00_u03b1_1641_, v_m_1642_, v_inst_1643_, v_f_1644_, v_x_1645_, v_x_342__boxed_1648_, v_x_343__boxed_1649_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1(lean_object* v_toApplicative_1651_, lean_object* v_tail_1652_, lean_object* v___x_1653_, lean_object* v_inst_1654_, lean_object* v___f_1655_, lean_object* v_____r_1656_){
_start:
{
lean_object* v_toPure_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v_toPure_1657_ = lean_ctor_get(v_toApplicative_1651_, 1);
lean_inc(v_toPure_1657_);
lean_dec_ref(v_toApplicative_1651_);
v___x_1658_ = lean_array_get_size(v_tail_1652_);
v___x_1659_ = lean_box(0);
v___x_1660_ = lean_nat_dec_lt(v___x_1653_, v___x_1658_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; 
lean_dec(v___f_1655_);
lean_dec_ref(v_inst_1654_);
lean_dec_ref(v_tail_1652_);
v___x_1661_ = lean_apply_2(v_toPure_1657_, lean_box(0), v___x_1659_);
return v___x_1661_;
}
else
{
uint8_t v___x_1662_; 
v___x_1662_ = lean_nat_dec_le(v___x_1658_, v___x_1658_);
if (v___x_1662_ == 0)
{
if (v___x_1660_ == 0)
{
lean_object* v___x_1663_; 
lean_dec(v___f_1655_);
lean_dec_ref(v_inst_1654_);
lean_dec_ref(v_tail_1652_);
v___x_1663_ = lean_apply_2(v_toPure_1657_, lean_box(0), v___x_1659_);
return v___x_1663_;
}
else
{
size_t v___x_1664_; size_t v___x_1665_; lean_object* v___x_1666_; 
lean_dec(v_toPure_1657_);
v___x_1664_ = ((size_t)0ULL);
v___x_1665_ = lean_usize_of_nat(v___x_1658_);
v___x_1666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1654_, v___f_1655_, v_tail_1652_, v___x_1664_, v___x_1665_, v___x_1659_);
return v___x_1666_;
}
}
else
{
size_t v___x_1667_; size_t v___x_1668_; lean_object* v___x_1669_; 
lean_dec(v_toPure_1657_);
v___x_1667_ = ((size_t)0ULL);
v___x_1668_ = lean_usize_of_nat(v___x_1658_);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1654_, v___f_1655_, v_tail_1652_, v___x_1667_, v___x_1668_, v___x_1659_);
return v___x_1669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1___boxed(lean_object* v_toApplicative_1670_, lean_object* v_tail_1671_, lean_object* v___x_1672_, lean_object* v_inst_1673_, lean_object* v___f_1674_, lean_object* v_____r_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_PersistentArray_forM___redArg___lam__1(v_toApplicative_1670_, v_tail_1671_, v___x_1672_, v_inst_1673_, v___f_1674_, v_____r_1675_);
lean_dec(v___x_1672_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg(lean_object* v_inst_1677_, lean_object* v_t_1678_, lean_object* v_f_1679_, lean_object* v_start_1680_){
_start:
{
lean_object* v_toApplicative_1681_; lean_object* v_toBind_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; 
v_toApplicative_1681_ = lean_ctor_get(v_inst_1677_, 0);
v_toBind_1682_ = lean_ctor_get(v_inst_1677_, 1);
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_nat_dec_eq(v_start_1680_, v___x_1683_);
if (v___x_1684_ == 0)
{
lean_object* v_root_1685_; lean_object* v_tail_1686_; size_t v_shift_1687_; lean_object* v_tailOff_1688_; uint8_t v___x_1689_; 
v_root_1685_ = lean_ctor_get(v_t_1678_, 0);
lean_inc_ref(v_root_1685_);
v_tail_1686_ = lean_ctor_get(v_t_1678_, 1);
lean_inc_ref(v_tail_1686_);
v_shift_1687_ = lean_ctor_get_usize(v_t_1678_, 4);
v_tailOff_1688_ = lean_ctor_get(v_t_1678_, 3);
lean_inc(v_tailOff_1688_);
lean_dec_ref(v_t_1678_);
v___x_1689_ = lean_nat_dec_le(v_tailOff_1688_, v_start_1680_);
if (v___x_1689_ == 0)
{
lean_object* v___f_1690_; lean_object* v___f_1691_; size_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_inc(v_toBind_1682_);
lean_dec(v_tailOff_1688_);
lean_inc(v_f_1679_);
v___f_1690_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1690_, 0, v_f_1679_);
lean_inc_ref(v_inst_1677_);
lean_inc_ref(v_toApplicative_1681_);
v___f_1691_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1691_, 0, v_toApplicative_1681_);
lean_closure_set(v___f_1691_, 1, v_tail_1686_);
lean_closure_set(v___f_1691_, 2, v___x_1683_);
lean_closure_set(v___f_1691_, 3, v_inst_1677_);
lean_closure_set(v___f_1691_, 4, v___f_1690_);
v___x_1692_ = lean_usize_of_nat(v_start_1680_);
v___x_1693_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1677_, v_f_1679_, v_root_1685_, v___x_1692_, v_shift_1687_);
v___x_1694_ = lean_apply_4(v_toBind_1682_, lean_box(0), lean_box(0), v___x_1693_, v___f_1691_);
return v___x_1694_;
}
else
{
lean_object* v_toPure_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
lean_dec_ref(v_root_1685_);
v_toPure_1695_ = lean_ctor_get(v_toApplicative_1681_, 1);
v___x_1696_ = lean_nat_sub(v_start_1680_, v_tailOff_1688_);
lean_dec(v_tailOff_1688_);
v___x_1697_ = lean_array_get_size(v_tail_1686_);
v___x_1698_ = lean_box(0);
v___x_1699_ = lean_nat_dec_lt(v___x_1696_, v___x_1697_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
lean_inc(v_toPure_1695_);
lean_dec(v___x_1696_);
lean_dec_ref(v_tail_1686_);
lean_dec(v_f_1679_);
lean_dec_ref(v_inst_1677_);
v___x_1700_ = lean_apply_2(v_toPure_1695_, lean_box(0), v___x_1698_);
return v___x_1700_;
}
else
{
lean_object* v___f_1701_; uint8_t v___x_1702_; 
v___f_1701_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1701_, 0, v_f_1679_);
v___x_1702_ = lean_nat_dec_le(v___x_1697_, v___x_1697_);
if (v___x_1702_ == 0)
{
if (v___x_1699_ == 0)
{
lean_object* v___x_1703_; 
lean_inc(v_toPure_1695_);
lean_dec_ref(v___f_1701_);
lean_dec(v___x_1696_);
lean_dec_ref(v_tail_1686_);
lean_dec_ref(v_inst_1677_);
v___x_1703_ = lean_apply_2(v_toPure_1695_, lean_box(0), v___x_1698_);
return v___x_1703_;
}
else
{
size_t v___x_1704_; size_t v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = lean_usize_of_nat(v___x_1696_);
lean_dec(v___x_1696_);
v___x_1705_ = lean_usize_of_nat(v___x_1697_);
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1677_, v___f_1701_, v_tail_1686_, v___x_1704_, v___x_1705_, v___x_1698_);
return v___x_1706_;
}
}
else
{
size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = lean_usize_of_nat(v___x_1696_);
lean_dec(v___x_1696_);
v___x_1708_ = lean_usize_of_nat(v___x_1697_);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1677_, v___f_1701_, v_tail_1686_, v___x_1707_, v___x_1708_, v___x_1698_);
return v___x_1709_;
}
}
}
}
else
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1677_, v_t_1678_, v_f_1679_);
return v___x_1710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___boxed(lean_object* v_inst_1711_, lean_object* v_t_1712_, lean_object* v_f_1713_, lean_object* v_start_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Lean_PersistentArray_forM___redArg(v_inst_1711_, v_t_1712_, v_f_1713_, v_start_1714_);
lean_dec(v_start_1714_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM(lean_object* v_00_u03b1_1716_, lean_object* v_m_1717_, lean_object* v_inst_1718_, lean_object* v_t_1719_, lean_object* v_f_1720_, lean_object* v_start_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_PersistentArray_forM___redArg(v_inst_1718_, v_t_1719_, v_f_1720_, v_start_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___boxed(lean_object* v_00_u03b1_1723_, lean_object* v_m_1724_, lean_object* v_inst_1725_, lean_object* v_t_1726_, lean_object* v_f_1727_, lean_object* v_start_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l_Lean_PersistentArray_forM(v_00_u03b1_1723_, v_m_1724_, v_inst_1725_, v_t_1726_, v_f_1727_, v_start_1728_);
lean_dec(v_start_1728_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___lam__0(lean_object* v_f_1730_, lean_object* v_x1_1731_, lean_object* v_x2_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = lean_apply_2(v_f_1730_, v_x1_1731_, v_x2_1732_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg(lean_object* v_t_1753_, lean_object* v_f_1754_, lean_object* v_init_1755_, lean_object* v_start_1756_){
_start:
{
lean_object* v___f_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1757_, 0, v_f_1754_);
v___x_1758_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1759_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1758_, v_t_1753_, v___f_1757_, v_init_1755_, v_start_1756_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___boxed(lean_object* v_t_1760_, lean_object* v_f_1761_, lean_object* v_init_1762_, lean_object* v_start_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_PersistentArray_foldl___redArg(v_t_1760_, v_f_1761_, v_init_1762_, v_start_1763_);
lean_dec(v_start_1763_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl(lean_object* v_00_u03b1_1765_, lean_object* v_00_u03b2_1766_, lean_object* v_t_1767_, lean_object* v_f_1768_, lean_object* v_init_1769_, lean_object* v_start_1770_){
_start:
{
lean_object* v___f_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___f_1771_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1771_, 0, v_f_1768_);
v___x_1772_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1773_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1772_, v_t_1767_, v___f_1771_, v_init_1769_, v_start_1770_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_00_u03b2_1775_, lean_object* v_t_1776_, lean_object* v_f_1777_, lean_object* v_init_1778_, lean_object* v_start_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_Lean_PersistentArray_foldl(v_00_u03b1_1774_, v_00_u03b2_1775_, v_t_1776_, v_f_1777_, v_init_1778_, v_start_1779_);
lean_dec(v_start_1779_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr___redArg(lean_object* v_t_1781_, lean_object* v_f_1782_, lean_object* v_init_1783_){
_start:
{
lean_object* v___f_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___f_1784_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1784_, 0, v_f_1782_);
v___x_1785_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1786_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1785_, v_t_1781_, v___f_1784_, v_init_1783_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr(lean_object* v_00_u03b1_1787_, lean_object* v_00_u03b2_1788_, lean_object* v_t_1789_, lean_object* v_f_1790_, lean_object* v_init_1791_){
_start:
{
lean_object* v___f_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___f_1792_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1792_, 0, v_f_1790_);
v___x_1793_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1794_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1793_, v_t_1789_, v___f_1792_, v_init_1791_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg___lam__0(lean_object* v_p_1795_, lean_object* v_x1_1796_, lean_object* v_x2_1797_){
_start:
{
lean_object* v___x_1798_; uint8_t v___x_1799_; 
lean_inc(v_x2_1797_);
v___x_1798_ = lean_apply_1(v_p_1795_, v_x2_1797_);
v___x_1799_ = lean_unbox(v___x_1798_);
if (v___x_1799_ == 0)
{
lean_dec(v_x2_1797_);
return v_x1_1796_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Lean_PersistentArray_push___redArg(v_x1_1796_, v_x2_1797_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg(lean_object* v_as_1801_, lean_object* v_p_1802_){
_start:
{
lean_object* v___f_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___f_1803_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1803_, 0, v_p_1802_);
v___x_1804_ = lean_unsigned_to_nat(32u);
v___x_1805_ = lean_mk_empty_array_with_capacity(v___x_1804_);
lean_dec_ref(v___x_1805_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_1808_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1809_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1808_, v_as_1801_, v___f_1803_, v___x_1807_, v___x_1806_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter(lean_object* v_00_u03b1_1810_, lean_object* v_as_1811_, lean_object* v_p_1812_){
_start:
{
lean_object* v___f_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___f_1813_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1813_, 0, v_p_1812_);
v___x_1814_ = lean_unsigned_to_nat(32u);
v___x_1815_ = lean_mk_empty_array_with_capacity(v___x_1814_);
lean_dec_ref(v___x_1815_);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_1818_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1819_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1818_, v_as_1811_, v___f_1813_, v___x_1817_, v___x_1816_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(lean_object* v_as_1820_, size_t v_i_1821_, size_t v_stop_1822_, lean_object* v_b_1823_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_usize_dec_eq(v_i_1821_, v_stop_1822_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; lean_object* v___x_1826_; size_t v___x_1827_; size_t v___x_1828_; 
v___x_1825_ = lean_array_uget_borrowed(v_as_1820_, v_i_1821_);
lean_inc(v___x_1825_);
v___x_1826_ = lean_array_push(v_b_1823_, v___x_1825_);
v___x_1827_ = ((size_t)1ULL);
v___x_1828_ = lean_usize_add(v_i_1821_, v___x_1827_);
v_i_1821_ = v___x_1828_;
v_b_1823_ = v___x_1826_;
goto _start;
}
else
{
return v_b_1823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg___boxed(lean_object* v_as_1830_, lean_object* v_i_1831_, lean_object* v_stop_1832_, lean_object* v_b_1833_){
_start:
{
size_t v_i_boxed_1834_; size_t v_stop_boxed_1835_; lean_object* v_res_1836_; 
v_i_boxed_1834_ = lean_unbox_usize(v_i_1831_);
lean_dec(v_i_1831_);
v_stop_boxed_1835_ = lean_unbox_usize(v_stop_1832_);
lean_dec(v_stop_1832_);
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1830_, v_i_boxed_1834_, v_stop_boxed_1835_, v_b_1833_);
lean_dec_ref(v_as_1830_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(lean_object* v_x_1837_, lean_object* v_x_1838_){
_start:
{
if (lean_obj_tag(v_x_1837_) == 0)
{
lean_object* v_cs_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___x_1842_; 
v_cs_1839_ = lean_ctor_get(v_x_1837_, 0);
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = lean_array_get_size(v_cs_1839_);
v___x_1842_ = lean_nat_dec_lt(v___x_1840_, v___x_1841_);
if (v___x_1842_ == 0)
{
return v_x_1838_;
}
else
{
size_t v___x_1843_; size_t v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = ((size_t)0ULL);
v___x_1844_ = lean_usize_of_nat(v___x_1841_);
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1839_, v___x_1843_, v___x_1844_, v_x_1838_);
return v___x_1845_;
}
}
else
{
lean_object* v_vs_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_vs_1846_ = lean_ctor_get(v_x_1837_, 0);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_array_get_size(v_vs_1846_);
v___x_1849_ = lean_nat_dec_lt(v___x_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
return v_x_1838_;
}
else
{
size_t v___x_1850_; size_t v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = ((size_t)0ULL);
v___x_1851_ = lean_usize_of_nat(v___x_1848_);
v___x_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1846_, v___x_1850_, v___x_1851_, v_x_1838_);
return v___x_1852_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(lean_object* v_as_1853_, size_t v_i_1854_, size_t v_stop_1855_, lean_object* v_b_1856_){
_start:
{
uint8_t v___x_1857_; 
v___x_1857_ = lean_usize_dec_eq(v_i_1854_, v_stop_1855_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; lean_object* v___x_1859_; size_t v___x_1860_; size_t v___x_1861_; 
v___x_1858_ = lean_array_uget_borrowed(v_as_1853_, v_i_1854_);
v___x_1859_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v___x_1858_, v_b_1856_);
v___x_1860_ = ((size_t)1ULL);
v___x_1861_ = lean_usize_add(v_i_1854_, v___x_1860_);
v_i_1854_ = v___x_1861_;
v_b_1856_ = v___x_1859_;
goto _start;
}
else
{
return v_b_1856_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_1863_, lean_object* v_i_1864_, lean_object* v_stop_1865_, lean_object* v_b_1866_){
_start:
{
size_t v_i_boxed_1867_; size_t v_stop_boxed_1868_; lean_object* v_res_1869_; 
v_i_boxed_1867_ = lean_unbox_usize(v_i_1864_);
lean_dec(v_i_1864_);
v_stop_boxed_1868_ = lean_unbox_usize(v_stop_1865_);
lean_dec(v_stop_1865_);
v_res_1869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1863_, v_i_boxed_1867_, v_stop_boxed_1868_, v_b_1866_);
lean_dec_ref(v_as_1863_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(lean_object* v_x_1870_, lean_object* v_x_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1870_, v_x_1871_);
lean_dec_ref(v_x_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(lean_object* v_x_1873_, size_t v_x_1874_, size_t v_x_1875_, lean_object* v_x_1876_){
_start:
{
if (lean_obj_tag(v_x_1873_) == 0)
{
lean_object* v_cs_1877_; lean_object* v___x_1878_; size_t v___x_1879_; lean_object* v_j_1880_; lean_object* v___x_1881_; size_t v___x_1882_; size_t v___x_1883_; size_t v___x_1884_; size_t v___x_1885_; size_t v___x_1886_; size_t v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_cs_1877_ = lean_ctor_get(v_x_1873_, 0);
v___x_1878_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_1879_ = lean_usize_shift_right(v_x_1874_, v_x_1875_);
v_j_1880_ = lean_usize_to_nat(v___x_1879_);
v___x_1881_ = lean_array_get_borrowed(v___x_1878_, v_cs_1877_, v_j_1880_);
v___x_1882_ = ((size_t)1ULL);
v___x_1883_ = lean_usize_shift_left(v___x_1882_, v_x_1875_);
v___x_1884_ = lean_usize_sub(v___x_1883_, v___x_1882_);
v___x_1885_ = lean_usize_land(v_x_1874_, v___x_1884_);
v___x_1886_ = ((size_t)5ULL);
v___x_1887_ = lean_usize_sub(v_x_1875_, v___x_1886_);
v___x_1888_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v___x_1881_, v___x_1885_, v___x_1887_, v_x_1876_);
v___x_1889_ = lean_unsigned_to_nat(1u);
v___x_1890_ = lean_nat_add(v_j_1880_, v___x_1889_);
lean_dec(v_j_1880_);
v___x_1891_ = lean_array_get_size(v_cs_1877_);
v___x_1892_ = lean_nat_dec_lt(v___x_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_dec(v___x_1890_);
return v___x_1888_;
}
else
{
size_t v___x_1893_; size_t v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_usize_of_nat(v___x_1890_);
lean_dec(v___x_1890_);
v___x_1894_ = lean_usize_of_nat(v___x_1891_);
v___x_1895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1877_, v___x_1893_, v___x_1894_, v___x_1888_);
return v___x_1895_;
}
}
else
{
lean_object* v_vs_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v_vs_1896_ = lean_ctor_get(v_x_1873_, 0);
v___x_1897_ = lean_usize_to_nat(v_x_1874_);
v___x_1898_ = lean_array_get_size(v_vs_1896_);
v___x_1899_ = lean_nat_dec_lt(v___x_1897_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_dec(v___x_1897_);
return v_x_1876_;
}
else
{
size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = lean_usize_of_nat(v___x_1897_);
lean_dec(v___x_1897_);
v___x_1901_ = lean_usize_of_nat(v___x_1898_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1896_, v___x_1900_, v___x_1901_, v_x_1876_);
return v___x_1902_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_x_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_){
_start:
{
size_t v_x_1118__boxed_1907_; size_t v_x_1119__boxed_1908_; lean_object* v_res_1909_; 
v_x_1118__boxed_1907_ = lean_unbox_usize(v_x_1904_);
lean_dec(v_x_1904_);
v_x_1119__boxed_1908_ = lean_unbox_usize(v_x_1905_);
lean_dec(v_x_1905_);
v_res_1909_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1903_, v_x_1118__boxed_1907_, v_x_1119__boxed_1908_, v_x_1906_);
lean_dec_ref(v_x_1903_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(lean_object* v_t_1910_, lean_object* v_init_1911_, lean_object* v_start_1912_){
_start:
{
lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1913_ = lean_unsigned_to_nat(0u);
v___x_1914_ = lean_nat_dec_eq(v_start_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v_root_1915_; lean_object* v_tail_1916_; size_t v_shift_1917_; lean_object* v_tailOff_1918_; uint8_t v___x_1919_; 
v_root_1915_ = lean_ctor_get(v_t_1910_, 0);
v_tail_1916_ = lean_ctor_get(v_t_1910_, 1);
v_shift_1917_ = lean_ctor_get_usize(v_t_1910_, 4);
v_tailOff_1918_ = lean_ctor_get(v_t_1910_, 3);
v___x_1919_ = lean_nat_dec_le(v_tailOff_1918_, v_start_1912_);
if (v___x_1919_ == 0)
{
size_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1920_ = lean_usize_of_nat(v_start_1912_);
v___x_1921_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_root_1915_, v___x_1920_, v_shift_1917_, v_init_1911_);
v___x_1922_ = lean_array_get_size(v_tail_1916_);
v___x_1923_ = lean_nat_dec_lt(v___x_1913_, v___x_1922_);
if (v___x_1923_ == 0)
{
return v___x_1921_;
}
else
{
size_t v___x_1924_; size_t v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = ((size_t)0ULL);
v___x_1925_ = lean_usize_of_nat(v___x_1922_);
v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1916_, v___x_1924_, v___x_1925_, v___x_1921_);
return v___x_1926_;
}
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1927_ = lean_nat_sub(v_start_1912_, v_tailOff_1918_);
v___x_1928_ = lean_array_get_size(v_tail_1916_);
v___x_1929_ = lean_nat_dec_lt(v___x_1927_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_dec(v___x_1927_);
return v_init_1911_;
}
else
{
size_t v___x_1930_; size_t v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_usize_of_nat(v___x_1927_);
lean_dec(v___x_1927_);
v___x_1931_ = lean_usize_of_nat(v___x_1928_);
v___x_1932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1916_, v___x_1930_, v___x_1931_, v_init_1911_);
return v___x_1932_;
}
}
}
else
{
lean_object* v_root_1933_; lean_object* v_tail_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v_root_1933_ = lean_ctor_get(v_t_1910_, 0);
v_tail_1934_ = lean_ctor_get(v_t_1910_, 1);
v___x_1935_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_root_1933_, v_init_1911_);
v___x_1936_ = lean_array_get_size(v_tail_1934_);
v___x_1937_ = lean_nat_dec_lt(v___x_1913_, v___x_1936_);
if (v___x_1937_ == 0)
{
return v___x_1935_;
}
else
{
size_t v___x_1938_; size_t v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = lean_usize_of_nat(v___x_1936_);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1934_, v___x_1938_, v___x_1939_, v___x_1935_);
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(lean_object* v_t_1941_, lean_object* v_init_1942_, lean_object* v_start_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1941_, v_init_1942_, v_start_1943_);
lean_dec(v_start_1943_);
lean_dec_ref(v_t_1941_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object* v_t_1945_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = lean_unsigned_to_nat(0u);
v___x_1947_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
v___x_1948_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1945_, v___x_1947_, v___x_1946_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg___boxed(lean_object* v_t_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_PersistentArray_toArray___redArg(v_t_1949_);
lean_dec_ref(v_t_1949_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray(lean_object* v_00_u03b1_1951_, lean_object* v_t_1952_){
_start:
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_PersistentArray_toArray___redArg(v_t_1952_);
return v___x_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___boxed(lean_object* v_00_u03b1_1954_, lean_object* v_t_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_PersistentArray_toArray(v_00_u03b1_1954_, v_t_1955_);
lean_dec_ref(v_t_1955_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(lean_object* v_00_u03b1_1957_, lean_object* v_t_1958_, lean_object* v_init_1959_, lean_object* v_start_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1958_, v_init_1959_, v_start_1960_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(lean_object* v_00_u03b1_1962_, lean_object* v_t_1963_, lean_object* v_init_1964_, lean_object* v_start_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(v_00_u03b1_1962_, v_t_1963_, v_init_1964_, v_start_1965_);
lean_dec(v_start_1965_);
lean_dec_ref(v_t_1963_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(lean_object* v_00_u03b1_1967_, lean_object* v_x_1968_, size_t v_x_1969_, size_t v_x_1970_, lean_object* v_x_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1968_, v_x_1969_, v_x_1970_, v_x_1971_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_){
_start:
{
size_t v_x_1236__boxed_1978_; size_t v_x_1237__boxed_1979_; lean_object* v_res_1980_; 
v_x_1236__boxed_1978_ = lean_unbox_usize(v_x_1975_);
lean_dec(v_x_1975_);
v_x_1237__boxed_1979_ = lean_unbox_usize(v_x_1976_);
lean_dec(v_x_1976_);
v_res_1980_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(v_00_u03b1_1973_, v_x_1974_, v_x_1236__boxed_1978_, v_x_1237__boxed_1979_, v_x_1977_);
lean_dec_ref(v_x_1974_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(lean_object* v_00_u03b1_1981_, lean_object* v_as_1982_, size_t v_i_1983_, size_t v_stop_1984_, lean_object* v_b_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1982_, v_i_1983_, v_stop_1984_, v_b_1985_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1987_, lean_object* v_as_1988_, lean_object* v_i_1989_, lean_object* v_stop_1990_, lean_object* v_b_1991_){
_start:
{
size_t v_i_boxed_1992_; size_t v_stop_boxed_1993_; lean_object* v_res_1994_; 
v_i_boxed_1992_ = lean_unbox_usize(v_i_1989_);
lean_dec(v_i_1989_);
v_stop_boxed_1993_ = lean_unbox_usize(v_stop_1990_);
lean_dec(v_stop_1990_);
v_res_1994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(v_00_u03b1_1987_, v_as_1988_, v_i_boxed_1992_, v_stop_boxed_1993_, v_b_1991_);
lean_dec_ref(v_as_1988_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(lean_object* v_00_u03b1_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1996_, v_x_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(v_00_u03b1_1999_, v_x_2000_, v_x_2001_);
lean_dec_ref(v_x_2000_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2003_, lean_object* v_as_2004_, size_t v_i_2005_, size_t v_stop_2006_, lean_object* v_b_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_2004_, v_i_2005_, v_stop_2006_, v_b_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2009_, lean_object* v_as_2010_, lean_object* v_i_2011_, lean_object* v_stop_2012_, lean_object* v_b_2013_){
_start:
{
size_t v_i_boxed_2014_; size_t v_stop_boxed_2015_; lean_object* v_res_2016_; 
v_i_boxed_2014_ = lean_unbox_usize(v_i_2011_);
lean_dec(v_i_2011_);
v_stop_boxed_2015_ = lean_unbox_usize(v_stop_2012_);
lean_dec(v_stop_2012_);
v_res_2016_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(v_00_u03b1_2009_, v_as_2010_, v_i_boxed_2014_, v_stop_boxed_2015_, v_b_2013_);
lean_dec_ref(v_as_2010_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(lean_object* v_as_2017_, size_t v_i_2018_, size_t v_stop_2019_, lean_object* v_b_2020_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_usize_dec_eq(v_i_2018_, v_stop_2019_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; size_t v___x_2024_; size_t v___x_2025_; 
v___x_2022_ = lean_array_uget_borrowed(v_as_2017_, v_i_2018_);
lean_inc(v___x_2022_);
v___x_2023_ = l_Lean_PersistentArray_push___redArg(v_b_2020_, v___x_2022_);
v___x_2024_ = ((size_t)1ULL);
v___x_2025_ = lean_usize_add(v_i_2018_, v___x_2024_);
v_i_2018_ = v___x_2025_;
v_b_2020_ = v___x_2023_;
goto _start;
}
else
{
return v_b_2020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg___boxed(lean_object* v_as_2027_, lean_object* v_i_2028_, lean_object* v_stop_2029_, lean_object* v_b_2030_){
_start:
{
size_t v_i_boxed_2031_; size_t v_stop_boxed_2032_; lean_object* v_res_2033_; 
v_i_boxed_2031_ = lean_unbox_usize(v_i_2028_);
lean_dec(v_i_2028_);
v_stop_boxed_2032_ = lean_unbox_usize(v_stop_2029_);
lean_dec(v_stop_2029_);
v_res_2033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2027_, v_i_boxed_2031_, v_stop_boxed_2032_, v_b_2030_);
lean_dec_ref(v_as_2027_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
if (lean_obj_tag(v_x_2034_) == 0)
{
lean_object* v_cs_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v_cs_2036_ = lean_ctor_get(v_x_2034_, 0);
v___x_2037_ = lean_unsigned_to_nat(0u);
v___x_2038_ = lean_array_get_size(v_cs_2036_);
v___x_2039_ = lean_nat_dec_lt(v___x_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
return v_x_2035_;
}
else
{
size_t v___x_2040_; size_t v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = ((size_t)0ULL);
v___x_2041_ = lean_usize_of_nat(v___x_2038_);
v___x_2042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2036_, v___x_2040_, v___x_2041_, v_x_2035_);
return v___x_2042_;
}
}
else
{
lean_object* v_vs_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v_vs_2043_ = lean_ctor_get(v_x_2034_, 0);
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = lean_array_get_size(v_vs_2043_);
v___x_2046_ = lean_nat_dec_lt(v___x_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
return v_x_2035_;
}
else
{
size_t v___x_2047_; size_t v___x_2048_; lean_object* v___x_2049_; 
v___x_2047_ = ((size_t)0ULL);
v___x_2048_ = lean_usize_of_nat(v___x_2045_);
v___x_2049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2043_, v___x_2047_, v___x_2048_, v_x_2035_);
return v___x_2049_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2050_, size_t v_i_2051_, size_t v_stop_2052_, lean_object* v_b_2053_){
_start:
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_usize_dec_eq(v_i_2051_, v_stop_2052_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; size_t v___x_2057_; size_t v___x_2058_; 
v___x_2055_ = lean_array_uget_borrowed(v_as_2050_, v_i_2051_);
v___x_2056_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v___x_2055_, v_b_2053_);
v___x_2057_ = ((size_t)1ULL);
v___x_2058_ = lean_usize_add(v_i_2051_, v___x_2057_);
v_i_2051_ = v___x_2058_;
v_b_2053_ = v___x_2056_;
goto _start;
}
else
{
return v_b_2053_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2060_, lean_object* v_i_2061_, lean_object* v_stop_2062_, lean_object* v_b_2063_){
_start:
{
size_t v_i_boxed_2064_; size_t v_stop_boxed_2065_; lean_object* v_res_2066_; 
v_i_boxed_2064_ = lean_unbox_usize(v_i_2061_);
lean_dec(v_i_2061_);
v_stop_boxed_2065_ = lean_unbox_usize(v_stop_2062_);
lean_dec(v_stop_2062_);
v_res_2066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2060_, v_i_boxed_2064_, v_stop_boxed_2065_, v_b_2063_);
lean_dec_ref(v_as_2060_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2067_, v_x_2068_);
lean_dec_ref(v_x_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(lean_object* v_x_2070_, size_t v_x_2071_, size_t v_x_2072_, lean_object* v_x_2073_){
_start:
{
if (lean_obj_tag(v_x_2070_) == 0)
{
lean_object* v_cs_2074_; lean_object* v___x_2075_; size_t v___x_2076_; lean_object* v_j_2077_; lean_object* v___x_2078_; size_t v___x_2079_; size_t v___x_2080_; size_t v___x_2081_; size_t v___x_2082_; size_t v___x_2083_; size_t v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_cs_2074_ = lean_ctor_get(v_x_2070_, 0);
v___x_2075_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_2076_ = lean_usize_shift_right(v_x_2071_, v_x_2072_);
v_j_2077_ = lean_usize_to_nat(v___x_2076_);
v___x_2078_ = lean_array_get_borrowed(v___x_2075_, v_cs_2074_, v_j_2077_);
v___x_2079_ = ((size_t)1ULL);
v___x_2080_ = lean_usize_shift_left(v___x_2079_, v_x_2072_);
v___x_2081_ = lean_usize_sub(v___x_2080_, v___x_2079_);
v___x_2082_ = lean_usize_land(v_x_2071_, v___x_2081_);
v___x_2083_ = ((size_t)5ULL);
v___x_2084_ = lean_usize_sub(v_x_2072_, v___x_2083_);
v___x_2085_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v___x_2078_, v___x_2082_, v___x_2084_, v_x_2073_);
v___x_2086_ = lean_unsigned_to_nat(1u);
v___x_2087_ = lean_nat_add(v_j_2077_, v___x_2086_);
lean_dec(v_j_2077_);
v___x_2088_ = lean_array_get_size(v_cs_2074_);
v___x_2089_ = lean_nat_dec_lt(v___x_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_dec(v___x_2087_);
return v___x_2085_;
}
else
{
size_t v___x_2090_; size_t v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = lean_usize_of_nat(v___x_2087_);
lean_dec(v___x_2087_);
v___x_2091_ = lean_usize_of_nat(v___x_2088_);
v___x_2092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2074_, v___x_2090_, v___x_2091_, v___x_2085_);
return v___x_2092_;
}
}
else
{
lean_object* v_vs_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
v_vs_2093_ = lean_ctor_get(v_x_2070_, 0);
v___x_2094_ = lean_usize_to_nat(v_x_2071_);
v___x_2095_ = lean_array_get_size(v_vs_2093_);
v___x_2096_ = lean_nat_dec_lt(v___x_2094_, v___x_2095_);
if (v___x_2096_ == 0)
{
lean_dec(v___x_2094_);
return v_x_2073_;
}
else
{
size_t v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = lean_usize_of_nat(v___x_2094_);
lean_dec(v___x_2094_);
v___x_2098_ = lean_usize_of_nat(v___x_2095_);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2093_, v___x_2097_, v___x_2098_, v_x_2073_);
return v___x_2099_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(lean_object* v_x_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_, lean_object* v_x_2103_){
_start:
{
size_t v_x_1125__boxed_2104_; size_t v_x_1126__boxed_2105_; lean_object* v_res_2106_; 
v_x_1125__boxed_2104_ = lean_unbox_usize(v_x_2101_);
lean_dec(v_x_2101_);
v_x_1126__boxed_2105_ = lean_unbox_usize(v_x_2102_);
lean_dec(v_x_2102_);
v_res_2106_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2100_, v_x_1125__boxed_2104_, v_x_1126__boxed_2105_, v_x_2103_);
lean_dec_ref(v_x_2100_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(lean_object* v_t_2107_, lean_object* v_init_2108_, lean_object* v_start_2109_){
_start:
{
lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = lean_nat_dec_eq(v_start_2109_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v_root_2112_; lean_object* v_tail_2113_; size_t v_shift_2114_; lean_object* v_tailOff_2115_; uint8_t v___x_2116_; 
v_root_2112_ = lean_ctor_get(v_t_2107_, 0);
v_tail_2113_ = lean_ctor_get(v_t_2107_, 1);
v_shift_2114_ = lean_ctor_get_usize(v_t_2107_, 4);
v_tailOff_2115_ = lean_ctor_get(v_t_2107_, 3);
v___x_2116_ = lean_nat_dec_le(v_tailOff_2115_, v_start_2109_);
if (v___x_2116_ == 0)
{
size_t v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v___x_2117_ = lean_usize_of_nat(v_start_2109_);
v___x_2118_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_root_2112_, v___x_2117_, v_shift_2114_, v_init_2108_);
v___x_2119_ = lean_array_get_size(v_tail_2113_);
v___x_2120_ = lean_nat_dec_lt(v___x_2110_, v___x_2119_);
if (v___x_2120_ == 0)
{
return v___x_2118_;
}
else
{
size_t v___x_2121_; size_t v___x_2122_; lean_object* v___x_2123_; 
v___x_2121_ = ((size_t)0ULL);
v___x_2122_ = lean_usize_of_nat(v___x_2119_);
v___x_2123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2113_, v___x_2121_, v___x_2122_, v___x_2118_);
return v___x_2123_;
}
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2124_ = lean_nat_sub(v_start_2109_, v_tailOff_2115_);
v___x_2125_ = lean_array_get_size(v_tail_2113_);
v___x_2126_ = lean_nat_dec_lt(v___x_2124_, v___x_2125_);
if (v___x_2126_ == 0)
{
lean_dec(v___x_2124_);
return v_init_2108_;
}
else
{
size_t v___x_2127_; size_t v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_usize_of_nat(v___x_2124_);
lean_dec(v___x_2124_);
v___x_2128_ = lean_usize_of_nat(v___x_2125_);
v___x_2129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2113_, v___x_2127_, v___x_2128_, v_init_2108_);
return v___x_2129_;
}
}
}
else
{
lean_object* v_root_2130_; lean_object* v_tail_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v_root_2130_ = lean_ctor_get(v_t_2107_, 0);
v_tail_2131_ = lean_ctor_get(v_t_2107_, 1);
v___x_2132_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_root_2130_, v_init_2108_);
v___x_2133_ = lean_array_get_size(v_tail_2131_);
v___x_2134_ = lean_nat_dec_lt(v___x_2110_, v___x_2133_);
if (v___x_2134_ == 0)
{
return v___x_2132_;
}
else
{
size_t v___x_2135_; size_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = ((size_t)0ULL);
v___x_2136_ = lean_usize_of_nat(v___x_2133_);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2131_, v___x_2135_, v___x_2136_, v___x_2132_);
return v___x_2137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(lean_object* v_t_2138_, lean_object* v_init_2139_, lean_object* v_start_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2138_, v_init_2139_, v_start_2140_);
lean_dec(v_start_2140_);
lean_dec_ref(v_t_2138_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg(lean_object* v_t_u2081_2142_, lean_object* v_t_u2082_2143_){
_start:
{
uint8_t v___x_2144_; 
v___x_2144_ = l_Lean_PersistentArray_isEmpty___redArg(v_t_u2081_2142_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_u2082_2143_, v_t_u2081_2142_, v___x_2145_);
return v___x_2146_;
}
else
{
lean_dec_ref(v_t_u2081_2142_);
lean_inc_ref(v_t_u2082_2143_);
return v_t_u2082_2143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg___boxed(lean_object* v_t_u2081_2147_, lean_object* v_t_u2082_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2147_, v_t_u2082_2148_);
lean_dec_ref(v_t_u2082_2148_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append(lean_object* v_00_u03b1_2150_, lean_object* v_t_u2081_2151_, lean_object* v_t_u2082_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2151_, v_t_u2082_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___boxed(lean_object* v_00_u03b1_2154_, lean_object* v_t_u2081_2155_, lean_object* v_t_u2082_2156_){
_start:
{
lean_object* v_res_2157_; 
v_res_2157_ = l_Lean_PersistentArray_append(v_00_u03b1_2154_, v_t_u2081_2155_, v_t_u2082_2156_);
lean_dec_ref(v_t_u2082_2156_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(lean_object* v_00_u03b1_2158_, lean_object* v_t_2159_, lean_object* v_init_2160_, lean_object* v_start_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2159_, v_init_2160_, v_start_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(lean_object* v_00_u03b1_2163_, lean_object* v_t_2164_, lean_object* v_init_2165_, lean_object* v_start_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(v_00_u03b1_2163_, v_t_2164_, v_init_2165_, v_start_2166_);
lean_dec(v_start_2166_);
lean_dec_ref(v_t_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(lean_object* v_00_u03b1_2168_, lean_object* v_x_2169_, size_t v_x_2170_, size_t v_x_2171_, lean_object* v_x_2172_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2169_, v_x_2170_, v_x_2171_, v_x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_, lean_object* v_x_2178_){
_start:
{
size_t v_x_1241__boxed_2179_; size_t v_x_1242__boxed_2180_; lean_object* v_res_2181_; 
v_x_1241__boxed_2179_ = lean_unbox_usize(v_x_2176_);
lean_dec(v_x_2176_);
v_x_1242__boxed_2180_ = lean_unbox_usize(v_x_2177_);
lean_dec(v_x_2177_);
v_res_2181_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(v_00_u03b1_2174_, v_x_2175_, v_x_1241__boxed_2179_, v_x_1242__boxed_2180_, v_x_2178_);
lean_dec_ref(v_x_2175_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(lean_object* v_00_u03b1_2182_, lean_object* v_as_2183_, size_t v_i_2184_, size_t v_stop_2185_, lean_object* v_b_2186_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2183_, v_i_2184_, v_stop_2185_, v_b_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2188_, lean_object* v_as_2189_, lean_object* v_i_2190_, lean_object* v_stop_2191_, lean_object* v_b_2192_){
_start:
{
size_t v_i_boxed_2193_; size_t v_stop_boxed_2194_; lean_object* v_res_2195_; 
v_i_boxed_2193_ = lean_unbox_usize(v_i_2190_);
lean_dec(v_i_2190_);
v_stop_boxed_2194_ = lean_unbox_usize(v_stop_2191_);
lean_dec(v_stop_2191_);
v_res_2195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(v_00_u03b1_2188_, v_as_2189_, v_i_boxed_2193_, v_stop_boxed_2194_, v_b_2192_);
lean_dec_ref(v_as_2189_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(lean_object* v_00_u03b1_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2197_, v_x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(v_00_u03b1_2200_, v_x_2201_, v_x_2202_);
lean_dec_ref(v_x_2201_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2204_, lean_object* v_as_2205_, size_t v_i_2206_, size_t v_stop_2207_, lean_object* v_b_2208_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2205_, v_i_2206_, v_stop_2207_, v_b_2208_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2210_, lean_object* v_as_2211_, lean_object* v_i_2212_, lean_object* v_stop_2213_, lean_object* v_b_2214_){
_start:
{
size_t v_i_boxed_2215_; size_t v_stop_boxed_2216_; lean_object* v_res_2217_; 
v_i_boxed_2215_ = lean_unbox_usize(v_i_2212_);
lean_dec(v_i_2212_);
v_stop_boxed_2216_ = lean_unbox_usize(v_stop_2213_);
lean_dec(v_stop_2213_);
v_res_2217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(v_00_u03b1_2210_, v_as_2211_, v_i_boxed_2215_, v_stop_boxed_2216_, v_b_2214_);
lean_dec_ref(v_as_2211_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend___redArg(){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___redArg___closed__0));
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend___redArg___boxed(lean_object* v___dummy_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_PersistentArray_instAppend___redArg();
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend(lean_object* v_00_u03b1_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___redArg___closed__0));
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(lean_object* v_f_2225_, lean_object* v_x_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = lean_apply_1(v_f_2225_, v_x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg(lean_object* v_t_2228_, lean_object* v_f_2229_){
_start:
{
lean_object* v___f_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___f_2230_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2230_, 0, v_f_2229_);
v___x_2231_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2232_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2231_, v_t_2228_, v___f_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f(lean_object* v_00_u03b1_2233_, lean_object* v_00_u03b2_2234_, lean_object* v_t_2235_, lean_object* v_f_2236_){
_start:
{
lean_object* v___f_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___f_2237_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2237_, 0, v_f_2236_);
v___x_2238_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2239_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2238_, v_t_2235_, v___f_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f___redArg(lean_object* v_t_2240_, lean_object* v_f_2241_){
_start:
{
lean_object* v___f_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___f_2242_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2242_, 0, v_f_2241_);
v___x_2243_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2244_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2243_, v_t_2240_, v___f_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f(lean_object* v_00_u03b1_2245_, lean_object* v_00_u03b2_2246_, lean_object* v_t_2247_, lean_object* v_f_2248_){
_start:
{
lean_object* v___f_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___f_2249_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2249_, 0, v_f_2248_);
v___x_2250_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2251_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2250_, v_t_2247_, v___f_2249_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(lean_object* v_as_2252_, size_t v_i_2253_, size_t v_stop_2254_, lean_object* v_b_2255_){
_start:
{
uint8_t v___x_2256_; 
v___x_2256_ = lean_usize_dec_eq(v_i_2253_, v_stop_2254_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; size_t v___x_2259_; size_t v___x_2260_; 
v___x_2257_ = lean_array_uget_borrowed(v_as_2252_, v_i_2253_);
lean_inc(v___x_2257_);
v___x_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v_b_2255_);
v___x_2259_ = ((size_t)1ULL);
v___x_2260_ = lean_usize_add(v_i_2253_, v___x_2259_);
v_i_2253_ = v___x_2260_;
v_b_2255_ = v___x_2258_;
goto _start;
}
else
{
return v_b_2255_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg___boxed(lean_object* v_as_2262_, lean_object* v_i_2263_, lean_object* v_stop_2264_, lean_object* v_b_2265_){
_start:
{
size_t v_i_boxed_2266_; size_t v_stop_boxed_2267_; lean_object* v_res_2268_; 
v_i_boxed_2266_ = lean_unbox_usize(v_i_2263_);
lean_dec(v_i_2263_);
v_stop_boxed_2267_ = lean_unbox_usize(v_stop_2264_);
lean_dec(v_stop_2264_);
v_res_2268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2262_, v_i_boxed_2266_, v_stop_boxed_2267_, v_b_2265_);
lean_dec_ref(v_as_2262_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(lean_object* v_x_2269_, lean_object* v_x_2270_){
_start:
{
if (lean_obj_tag(v_x_2269_) == 0)
{
lean_object* v_cs_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_cs_2271_ = lean_ctor_get(v_x_2269_, 0);
v___x_2272_ = lean_unsigned_to_nat(0u);
v___x_2273_ = lean_array_get_size(v_cs_2271_);
v___x_2274_ = lean_nat_dec_lt(v___x_2272_, v___x_2273_);
if (v___x_2274_ == 0)
{
return v_x_2270_;
}
else
{
size_t v___x_2275_; size_t v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = ((size_t)0ULL);
v___x_2276_ = lean_usize_of_nat(v___x_2273_);
v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2271_, v___x_2275_, v___x_2276_, v_x_2270_);
return v___x_2277_;
}
}
else
{
lean_object* v_vs_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v_vs_2278_ = lean_ctor_get(v_x_2269_, 0);
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = lean_array_get_size(v_vs_2278_);
v___x_2281_ = lean_nat_dec_lt(v___x_2279_, v___x_2280_);
if (v___x_2281_ == 0)
{
return v_x_2270_;
}
else
{
size_t v___x_2282_; size_t v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = ((size_t)0ULL);
v___x_2283_ = lean_usize_of_nat(v___x_2280_);
v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2278_, v___x_2282_, v___x_2283_, v_x_2270_);
return v___x_2284_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2285_, size_t v_i_2286_, size_t v_stop_2287_, lean_object* v_b_2288_){
_start:
{
uint8_t v___x_2289_; 
v___x_2289_ = lean_usize_dec_eq(v_i_2286_, v_stop_2287_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2291_; size_t v___x_2292_; size_t v___x_2293_; 
v___x_2290_ = lean_array_uget_borrowed(v_as_2285_, v_i_2286_);
v___x_2291_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v___x_2290_, v_b_2288_);
v___x_2292_ = ((size_t)1ULL);
v___x_2293_ = lean_usize_add(v_i_2286_, v___x_2292_);
v_i_2286_ = v___x_2293_;
v_b_2288_ = v___x_2291_;
goto _start;
}
else
{
return v_b_2288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2295_, lean_object* v_i_2296_, lean_object* v_stop_2297_, lean_object* v_b_2298_){
_start:
{
size_t v_i_boxed_2299_; size_t v_stop_boxed_2300_; lean_object* v_res_2301_; 
v_i_boxed_2299_ = lean_unbox_usize(v_i_2296_);
lean_dec(v_i_2296_);
v_stop_boxed_2300_ = lean_unbox_usize(v_stop_2297_);
lean_dec(v_stop_2297_);
v_res_2301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2295_, v_i_boxed_2299_, v_stop_boxed_2300_, v_b_2298_);
lean_dec_ref(v_as_2295_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(lean_object* v_x_2302_, lean_object* v_x_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2302_, v_x_2303_);
lean_dec_ref(v_x_2302_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(lean_object* v_x_2305_, size_t v_x_2306_, size_t v_x_2307_, lean_object* v_x_2308_){
_start:
{
if (lean_obj_tag(v_x_2305_) == 0)
{
lean_object* v_cs_2309_; lean_object* v___x_2310_; size_t v___x_2311_; lean_object* v_j_2312_; lean_object* v___x_2313_; size_t v___x_2314_; size_t v___x_2315_; size_t v___x_2316_; size_t v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v_cs_2309_ = lean_ctor_get(v_x_2305_, 0);
v___x_2310_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode_default___closed__0, &l_Lean_instInhabitedPersistentArrayNode_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode_default___closed__0);
v___x_2311_ = lean_usize_shift_right(v_x_2306_, v_x_2307_);
v_j_2312_ = lean_usize_to_nat(v___x_2311_);
v___x_2313_ = lean_array_get_borrowed(v___x_2310_, v_cs_2309_, v_j_2312_);
v___x_2314_ = ((size_t)1ULL);
v___x_2315_ = lean_usize_shift_left(v___x_2314_, v_x_2307_);
v___x_2316_ = lean_usize_sub(v___x_2315_, v___x_2314_);
v___x_2317_ = lean_usize_land(v_x_2306_, v___x_2316_);
v___x_2318_ = ((size_t)5ULL);
v___x_2319_ = lean_usize_sub(v_x_2307_, v___x_2318_);
v___x_2320_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v___x_2313_, v___x_2317_, v___x_2319_, v_x_2308_);
v___x_2321_ = lean_unsigned_to_nat(1u);
v___x_2322_ = lean_nat_add(v_j_2312_, v___x_2321_);
lean_dec(v_j_2312_);
v___x_2323_ = lean_array_get_size(v_cs_2309_);
v___x_2324_ = lean_nat_dec_lt(v___x_2322_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_dec(v___x_2322_);
return v___x_2320_;
}
else
{
size_t v___x_2325_; size_t v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = lean_usize_of_nat(v___x_2322_);
lean_dec(v___x_2322_);
v___x_2326_ = lean_usize_of_nat(v___x_2323_);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2309_, v___x_2325_, v___x_2326_, v___x_2320_);
return v___x_2327_;
}
}
else
{
lean_object* v_vs_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; uint8_t v___x_2331_; 
v_vs_2328_ = lean_ctor_get(v_x_2305_, 0);
v___x_2329_ = lean_usize_to_nat(v_x_2306_);
v___x_2330_ = lean_array_get_size(v_vs_2328_);
v___x_2331_ = lean_nat_dec_lt(v___x_2329_, v___x_2330_);
if (v___x_2331_ == 0)
{
lean_dec(v___x_2329_);
return v_x_2308_;
}
else
{
size_t v___x_2332_; size_t v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = lean_usize_of_nat(v___x_2329_);
lean_dec(v___x_2329_);
v___x_2333_ = lean_usize_of_nat(v___x_2330_);
v___x_2334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2328_, v___x_2332_, v___x_2333_, v_x_2308_);
return v___x_2334_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_){
_start:
{
size_t v_x_1119__boxed_2339_; size_t v_x_1120__boxed_2340_; lean_object* v_res_2341_; 
v_x_1119__boxed_2339_ = lean_unbox_usize(v_x_2336_);
lean_dec(v_x_2336_);
v_x_1120__boxed_2340_ = lean_unbox_usize(v_x_2337_);
lean_dec(v_x_2337_);
v_res_2341_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2335_, v_x_1119__boxed_2339_, v_x_1120__boxed_2340_, v_x_2338_);
lean_dec_ref(v_x_2335_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(lean_object* v_t_2342_, lean_object* v_init_2343_, lean_object* v_start_2344_){
_start:
{
lean_object* v___x_2345_; uint8_t v___x_2346_; 
v___x_2345_ = lean_unsigned_to_nat(0u);
v___x_2346_ = lean_nat_dec_eq(v_start_2344_, v___x_2345_);
if (v___x_2346_ == 0)
{
lean_object* v_root_2347_; lean_object* v_tail_2348_; size_t v_shift_2349_; lean_object* v_tailOff_2350_; uint8_t v___x_2351_; 
v_root_2347_ = lean_ctor_get(v_t_2342_, 0);
v_tail_2348_ = lean_ctor_get(v_t_2342_, 1);
v_shift_2349_ = lean_ctor_get_usize(v_t_2342_, 4);
v_tailOff_2350_ = lean_ctor_get(v_t_2342_, 3);
v___x_2351_ = lean_nat_dec_le(v_tailOff_2350_, v_start_2344_);
if (v___x_2351_ == 0)
{
size_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2352_ = lean_usize_of_nat(v_start_2344_);
v___x_2353_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_root_2347_, v___x_2352_, v_shift_2349_, v_init_2343_);
v___x_2354_ = lean_array_get_size(v_tail_2348_);
v___x_2355_ = lean_nat_dec_lt(v___x_2345_, v___x_2354_);
if (v___x_2355_ == 0)
{
return v___x_2353_;
}
else
{
size_t v___x_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = ((size_t)0ULL);
v___x_2357_ = lean_usize_of_nat(v___x_2354_);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2348_, v___x_2356_, v___x_2357_, v___x_2353_);
return v___x_2358_;
}
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v___x_2359_ = lean_nat_sub(v_start_2344_, v_tailOff_2350_);
v___x_2360_ = lean_array_get_size(v_tail_2348_);
v___x_2361_ = lean_nat_dec_lt(v___x_2359_, v___x_2360_);
if (v___x_2361_ == 0)
{
lean_dec(v___x_2359_);
return v_init_2343_;
}
else
{
size_t v___x_2362_; size_t v___x_2363_; lean_object* v___x_2364_; 
v___x_2362_ = lean_usize_of_nat(v___x_2359_);
lean_dec(v___x_2359_);
v___x_2363_ = lean_usize_of_nat(v___x_2360_);
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2348_, v___x_2362_, v___x_2363_, v_init_2343_);
return v___x_2364_;
}
}
}
else
{
lean_object* v_root_2365_; lean_object* v_tail_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; uint8_t v___x_2369_; 
v_root_2365_ = lean_ctor_get(v_t_2342_, 0);
v_tail_2366_ = lean_ctor_get(v_t_2342_, 1);
v___x_2367_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_root_2365_, v_init_2343_);
v___x_2368_ = lean_array_get_size(v_tail_2366_);
v___x_2369_ = lean_nat_dec_lt(v___x_2345_, v___x_2368_);
if (v___x_2369_ == 0)
{
return v___x_2367_;
}
else
{
size_t v___x_2370_; size_t v___x_2371_; lean_object* v___x_2372_; 
v___x_2370_ = ((size_t)0ULL);
v___x_2371_ = lean_usize_of_nat(v___x_2368_);
v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2366_, v___x_2370_, v___x_2371_, v___x_2367_);
return v___x_2372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(lean_object* v_t_2373_, lean_object* v_init_2374_, lean_object* v_start_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2373_, v_init_2374_, v_start_2375_);
lean_dec(v_start_2375_);
lean_dec_ref(v_t_2373_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg(lean_object* v_t_2377_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2378_ = lean_box(0);
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2377_, v___x_2378_, v___x_2379_);
v___x_2381_ = l_List_reverse___redArg(v___x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg___boxed(lean_object* v_t_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_PersistentArray_toList___redArg(v_t_2382_);
lean_dec_ref(v_t_2382_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList(lean_object* v_00_u03b1_2384_, lean_object* v_t_2385_){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = l_Lean_PersistentArray_toList___redArg(v_t_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___boxed(lean_object* v_00_u03b1_2387_, lean_object* v_t_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_PersistentArray_toList(v_00_u03b1_2387_, v_t_2388_);
lean_dec_ref(v_t_2388_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(lean_object* v_00_u03b1_2390_, lean_object* v_t_2391_, lean_object* v_init_2392_, lean_object* v_start_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2391_, v_init_2392_, v_start_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_t_2396_, lean_object* v_init_2397_, lean_object* v_start_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(v_00_u03b1_2395_, v_t_2396_, v_init_2397_, v_start_2398_);
lean_dec(v_start_2398_);
lean_dec_ref(v_t_2396_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(lean_object* v_00_u03b1_2400_, lean_object* v_x_2401_, size_t v_x_2402_, size_t v_x_2403_, lean_object* v_x_2404_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2401_, v_x_2402_, v_x_2403_, v_x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2406_, lean_object* v_x_2407_, lean_object* v_x_2408_, lean_object* v_x_2409_, lean_object* v_x_2410_){
_start:
{
size_t v_x_1237__boxed_2411_; size_t v_x_1238__boxed_2412_; lean_object* v_res_2413_; 
v_x_1237__boxed_2411_ = lean_unbox_usize(v_x_2408_);
lean_dec(v_x_2408_);
v_x_1238__boxed_2412_ = lean_unbox_usize(v_x_2409_);
lean_dec(v_x_2409_);
v_res_2413_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(v_00_u03b1_2406_, v_x_2407_, v_x_1237__boxed_2411_, v_x_1238__boxed_2412_, v_x_2410_);
lean_dec_ref(v_x_2407_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(lean_object* v_00_u03b1_2414_, lean_object* v_as_2415_, size_t v_i_2416_, size_t v_stop_2417_, lean_object* v_b_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2415_, v_i_2416_, v_stop_2417_, v_b_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2420_, lean_object* v_as_2421_, lean_object* v_i_2422_, lean_object* v_stop_2423_, lean_object* v_b_2424_){
_start:
{
size_t v_i_boxed_2425_; size_t v_stop_boxed_2426_; lean_object* v_res_2427_; 
v_i_boxed_2425_ = lean_unbox_usize(v_i_2422_);
lean_dec(v_i_2422_);
v_stop_boxed_2426_ = lean_unbox_usize(v_stop_2423_);
lean_dec(v_stop_2423_);
v_res_2427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(v_00_u03b1_2420_, v_as_2421_, v_i_boxed_2425_, v_stop_boxed_2426_, v_b_2424_);
lean_dec_ref(v_as_2421_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(lean_object* v_00_u03b1_2428_, lean_object* v_x_2429_, lean_object* v_x_2430_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2429_, v_x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2432_, lean_object* v_x_2433_, lean_object* v_x_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(v_00_u03b1_2432_, v_x_2433_, v_x_2434_);
lean_dec_ref(v_x_2433_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2436_, lean_object* v_as_2437_, size_t v_i_2438_, size_t v_stop_2439_, lean_object* v_b_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2437_, v_i_2438_, v_stop_2439_, v_b_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2442_, lean_object* v_as_2443_, lean_object* v_i_2444_, lean_object* v_stop_2445_, lean_object* v_b_2446_){
_start:
{
size_t v_i_boxed_2447_; size_t v_stop_boxed_2448_; lean_object* v_res_2449_; 
v_i_boxed_2447_ = lean_unbox_usize(v_i_2444_);
lean_dec(v_i_2444_);
v_stop_boxed_2448_ = lean_unbox_usize(v_stop_2445_);
lean_dec(v_stop_2445_);
v_res_2449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(v_00_u03b1_2442_, v_as_2443_, v_i_boxed_2447_, v_stop_boxed_2448_, v_b_2446_);
lean_dec_ref(v_as_2443_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg(lean_object* v_inst_2450_, lean_object* v_p_2451_, lean_object* v_x_2452_){
_start:
{
if (lean_obj_tag(v_x_2452_) == 0)
{
lean_object* v_toApplicative_2453_; lean_object* v_cs_2454_; lean_object* v_toPure_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; 
v_toApplicative_2453_ = lean_ctor_get(v_inst_2450_, 0);
v_cs_2454_ = lean_ctor_get(v_x_2452_, 0);
lean_inc_ref(v_cs_2454_);
lean_dec_ref_known(v_x_2452_, 1);
v_toPure_2455_ = lean_ctor_get(v_toApplicative_2453_, 1);
v___x_2456_ = lean_unsigned_to_nat(0u);
v___x_2457_ = lean_array_get_size(v_cs_2454_);
v___x_2458_ = lean_nat_dec_lt(v___x_2456_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
lean_inc(v_toPure_2455_);
lean_dec_ref(v_cs_2454_);
lean_dec(v_p_2451_);
lean_dec_ref(v_inst_2450_);
v___x_2459_ = lean_box(v___x_2458_);
v___x_2460_ = lean_apply_2(v_toPure_2455_, lean_box(0), v___x_2459_);
return v___x_2460_;
}
else
{
if (v___x_2458_ == 0)
{
lean_object* v___x_2461_; lean_object* v___x_2462_; 
lean_inc(v_toPure_2455_);
lean_dec_ref(v_cs_2454_);
lean_dec(v_p_2451_);
lean_dec_ref(v_inst_2450_);
v___x_2461_ = lean_box(v___x_2458_);
v___x_2462_ = lean_apply_2(v_toPure_2455_, lean_box(0), v___x_2461_);
return v___x_2462_;
}
else
{
lean_object* v___f_2463_; size_t v___x_2464_; size_t v___x_2465_; lean_object* v___x_2466_; 
lean_inc_ref(v_inst_2450_);
v___f_2463_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2463_, 0, v_inst_2450_);
lean_closure_set(v___f_2463_, 1, v_p_2451_);
v___x_2464_ = ((size_t)0ULL);
v___x_2465_ = lean_usize_of_nat(v___x_2457_);
v___x_2466_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2450_, v___f_2463_, v_cs_2454_, v___x_2464_, v___x_2465_);
return v___x_2466_;
}
}
}
else
{
lean_object* v_toApplicative_2467_; lean_object* v_vs_2468_; lean_object* v_toPure_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v_toApplicative_2467_ = lean_ctor_get(v_inst_2450_, 0);
v_vs_2468_ = lean_ctor_get(v_x_2452_, 0);
lean_inc_ref(v_vs_2468_);
lean_dec_ref_known(v_x_2452_, 1);
v_toPure_2469_ = lean_ctor_get(v_toApplicative_2467_, 1);
v___x_2470_ = lean_unsigned_to_nat(0u);
v___x_2471_ = lean_array_get_size(v_vs_2468_);
v___x_2472_ = lean_nat_dec_lt(v___x_2470_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_inc(v_toPure_2469_);
lean_dec_ref(v_vs_2468_);
lean_dec(v_p_2451_);
lean_dec_ref(v_inst_2450_);
v___x_2473_ = lean_box(v___x_2472_);
v___x_2474_ = lean_apply_2(v_toPure_2469_, lean_box(0), v___x_2473_);
return v___x_2474_;
}
else
{
if (v___x_2472_ == 0)
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
lean_inc(v_toPure_2469_);
lean_dec_ref(v_vs_2468_);
lean_dec(v_p_2451_);
lean_dec_ref(v_inst_2450_);
v___x_2475_ = lean_box(v___x_2472_);
v___x_2476_ = lean_apply_2(v_toPure_2469_, lean_box(0), v___x_2475_);
return v___x_2476_;
}
else
{
size_t v___x_2477_; size_t v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = ((size_t)0ULL);
v___x_2478_ = lean_usize_of_nat(v___x_2471_);
v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2450_, v_p_2451_, v_vs_2468_, v___x_2477_, v___x_2478_);
return v___x_2479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg___lam__0(lean_object* v_inst_2480_, lean_object* v_p_2481_, lean_object* v_c_2482_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2480_, v_p_2481_, v_c_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux(lean_object* v_00_u03b1_2484_, lean_object* v_m_2485_, lean_object* v_inst_2486_, lean_object* v_p_2487_, lean_object* v_x_2488_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2486_, v_p_2487_, v_x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0(lean_object* v_tail_2490_, lean_object* v_toPure_2491_, lean_object* v_inst_2492_, lean_object* v_p_2493_, uint8_t v_b_2494_){
_start:
{
if (v_b_2494_ == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; 
v___x_2495_ = lean_unsigned_to_nat(0u);
v___x_2496_ = lean_array_get_size(v_tail_2490_);
v___x_2497_ = lean_nat_dec_lt(v___x_2495_, v___x_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
lean_dec(v_p_2493_);
lean_dec_ref(v_inst_2492_);
lean_dec_ref(v_tail_2490_);
v___x_2498_ = lean_box(v___x_2497_);
v___x_2499_ = lean_apply_2(v_toPure_2491_, lean_box(0), v___x_2498_);
return v___x_2499_;
}
else
{
if (v___x_2497_ == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_dec(v_p_2493_);
lean_dec_ref(v_inst_2492_);
lean_dec_ref(v_tail_2490_);
v___x_2500_ = lean_box(v___x_2497_);
v___x_2501_ = lean_apply_2(v_toPure_2491_, lean_box(0), v___x_2500_);
return v___x_2501_;
}
else
{
size_t v___x_2502_; size_t v___x_2503_; lean_object* v___x_2504_; 
lean_dec(v_toPure_2491_);
v___x_2502_ = ((size_t)0ULL);
v___x_2503_ = lean_usize_of_nat(v___x_2496_);
v___x_2504_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2492_, v_p_2493_, v_tail_2490_, v___x_2502_, v___x_2503_);
return v___x_2504_;
}
}
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec(v_p_2493_);
lean_dec_ref(v_inst_2492_);
lean_dec_ref(v_tail_2490_);
v___x_2505_ = lean_box(v_b_2494_);
v___x_2506_ = lean_apply_2(v_toPure_2491_, lean_box(0), v___x_2505_);
return v___x_2506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(lean_object* v_tail_2507_, lean_object* v_toPure_2508_, lean_object* v_inst_2509_, lean_object* v_p_2510_, lean_object* v_b_2511_){
_start:
{
uint8_t v_b_boxed_2512_; lean_object* v_res_2513_; 
v_b_boxed_2512_ = lean_unbox(v_b_2511_);
v_res_2513_ = l_Lean_PersistentArray_anyM___redArg___lam__0(v_tail_2507_, v_toPure_2508_, v_inst_2509_, v_p_2510_, v_b_boxed_2512_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object* v_inst_2514_, lean_object* v_t_2515_, lean_object* v_p_2516_){
_start:
{
lean_object* v_toApplicative_2517_; lean_object* v_toBind_2518_; lean_object* v_root_2519_; lean_object* v_tail_2520_; lean_object* v_toPure_2521_; lean_object* v___x_2522_; lean_object* v___f_2523_; lean_object* v___x_2524_; 
v_toApplicative_2517_ = lean_ctor_get(v_inst_2514_, 0);
v_toBind_2518_ = lean_ctor_get(v_inst_2514_, 1);
lean_inc(v_toBind_2518_);
v_root_2519_ = lean_ctor_get(v_t_2515_, 0);
lean_inc_ref(v_root_2519_);
v_tail_2520_ = lean_ctor_get(v_t_2515_, 1);
lean_inc_ref(v_tail_2520_);
lean_dec_ref(v_t_2515_);
v_toPure_2521_ = lean_ctor_get(v_toApplicative_2517_, 1);
lean_inc(v_toPure_2521_);
lean_inc(v_p_2516_);
lean_inc_ref(v_inst_2514_);
v___x_2522_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2514_, v_p_2516_, v_root_2519_);
v___f_2523_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2523_, 0, v_tail_2520_);
lean_closure_set(v___f_2523_, 1, v_toPure_2521_);
lean_closure_set(v___f_2523_, 2, v_inst_2514_);
lean_closure_set(v___f_2523_, 3, v_p_2516_);
v___x_2524_ = lean_apply_4(v_toBind_2518_, lean_box(0), lean_box(0), v___x_2522_, v___f_2523_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM(lean_object* v_00_u03b1_2525_, lean_object* v_m_2526_, lean_object* v_inst_2527_, lean_object* v_t_2528_, lean_object* v_p_2529_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2527_, v_t_2528_, v_p_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0(lean_object* v_toPure_2531_, uint8_t v_b_2532_){
_start:
{
if (v_b_2532_ == 0)
{
uint8_t v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = 1;
v___x_2534_ = lean_box(v___x_2533_);
v___x_2535_ = lean_apply_2(v_toPure_2531_, lean_box(0), v___x_2534_);
return v___x_2535_;
}
else
{
uint8_t v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = 0;
v___x_2537_ = lean_box(v___x_2536_);
v___x_2538_ = lean_apply_2(v_toPure_2531_, lean_box(0), v___x_2537_);
return v___x_2538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0___boxed(lean_object* v_toPure_2539_, lean_object* v_b_2540_){
_start:
{
uint8_t v_b_boxed_2541_; lean_object* v_res_2542_; 
v_b_boxed_2541_ = lean_unbox(v_b_2540_);
v_res_2542_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_2539_, v_b_boxed_2541_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__1(lean_object* v_p_2543_, lean_object* v_toBind_2544_, lean_object* v___f_2545_, lean_object* v_v_2546_){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_apply_1(v_p_2543_, v_v_2546_);
v___x_2548_ = lean_apply_4(v_toBind_2544_, lean_box(0), lean_box(0), v___x_2547_, v___f_2545_);
return v___x_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg(lean_object* v_inst_2549_, lean_object* v_a_2550_, lean_object* v_p_2551_){
_start:
{
lean_object* v_toApplicative_2552_; lean_object* v_toBind_2553_; lean_object* v_toPure_2554_; lean_object* v___f_2555_; lean_object* v___f_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_toApplicative_2552_ = lean_ctor_get(v_inst_2549_, 0);
v_toBind_2553_ = lean_ctor_get(v_inst_2549_, 1);
lean_inc_n(v_toBind_2553_, 2);
v_toPure_2554_ = lean_ctor_get(v_toApplicative_2552_, 1);
lean_inc(v_toPure_2554_);
v___f_2555_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2555_, 0, v_toPure_2554_);
lean_inc_ref(v___f_2555_);
v___f_2556_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2556_, 0, v_p_2551_);
lean_closure_set(v___f_2556_, 1, v_toBind_2553_);
lean_closure_set(v___f_2556_, 2, v___f_2555_);
v___x_2557_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2549_, v_a_2550_, v___f_2556_);
v___x_2558_ = lean_apply_4(v_toBind_2553_, lean_box(0), lean_box(0), v___x_2557_, v___f_2555_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM(lean_object* v_00_u03b1_2559_, lean_object* v_m_2560_, lean_object* v_inst_2561_, lean_object* v_a_2562_, lean_object* v_p_2563_){
_start:
{
lean_object* v_toApplicative_2564_; lean_object* v_toBind_2565_; lean_object* v_toPure_2566_; lean_object* v___f_2567_; lean_object* v___f_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_toApplicative_2564_ = lean_ctor_get(v_inst_2561_, 0);
v_toBind_2565_ = lean_ctor_get(v_inst_2561_, 1);
lean_inc_n(v_toBind_2565_, 2);
v_toPure_2566_ = lean_ctor_get(v_toApplicative_2564_, 1);
lean_inc(v_toPure_2566_);
v___f_2567_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2567_, 0, v_toPure_2566_);
lean_inc_ref(v___f_2567_);
v___f_2568_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2568_, 0, v_p_2563_);
lean_closure_set(v___f_2568_, 1, v_toBind_2565_);
lean_closure_set(v___f_2568_, 2, v___f_2567_);
v___x_2569_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2561_, v_a_2562_, v___f_2568_);
v___x_2570_ = lean_apply_4(v_toBind_2565_, lean_box(0), lean_box(0), v___x_2569_, v___f_2567_);
return v___x_2570_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg___lam__0(lean_object* v_p_2571_, lean_object* v_x_2572_){
_start:
{
lean_object* v___x_2573_; uint8_t v___x_2574_; 
v___x_2573_ = lean_apply_1(v_p_2571_, v_x_2572_);
v___x_2574_ = lean_unbox(v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___lam__0___boxed(lean_object* v_p_2575_, lean_object* v_x_2576_){
_start:
{
uint8_t v_res_2577_; lean_object* v_r_2578_; 
v_res_2577_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_2575_, v_x_2576_);
v_r_2578_ = lean_box(v_res_2577_);
return v_r_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg(lean_object* v_a_2579_, lean_object* v_p_2580_){
_start:
{
lean_object* v___f_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___f_2581_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2581_, 0, v_p_2580_);
v___x_2582_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2583_ = l_Lean_PersistentArray_anyM___redArg(v___x_2582_, v_a_2579_, v___f_2581_);
return v___x_2583_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any(lean_object* v_00_u03b1_2584_, lean_object* v_a_2585_, lean_object* v_p_2586_){
_start:
{
lean_object* v___f_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___f_2587_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2587_, 0, v_p_2586_);
v___x_2588_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2589_ = l_Lean_PersistentArray_anyM___redArg(v___x_2588_, v_a_2585_, v___f_2587_);
v___x_2590_ = lean_unbox(v___x_2589_);
lean_dec(v___x_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___boxed(lean_object* v_00_u03b1_2591_, lean_object* v_a_2592_, lean_object* v_p_2593_){
_start:
{
uint8_t v_res_2594_; lean_object* v_r_2595_; 
v_res_2594_ = l_Lean_PersistentArray_any(v_00_u03b1_2591_, v_a_2592_, v_p_2593_);
v_r_2595_ = lean_box(v_res_2594_);
return v_r_2595_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg___lam__0(lean_object* v_p_2596_, lean_object* v_x_2597_){
_start:
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = lean_apply_1(v_p_2596_, v_x_2597_);
v___x_2599_ = lean_unbox(v___x_2598_);
if (v___x_2599_ == 0)
{
uint8_t v___x_2600_; 
v___x_2600_ = 1;
return v___x_2600_;
}
else
{
uint8_t v___x_2601_; 
v___x_2601_ = 0;
return v___x_2601_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___lam__0___boxed(lean_object* v_p_2602_, lean_object* v_x_2603_){
_start:
{
uint8_t v_res_2604_; lean_object* v_r_2605_; 
v_res_2604_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_2602_, v_x_2603_);
v_r_2605_ = lean_box(v_res_2604_);
return v_r_2605_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg(lean_object* v_a_2606_, lean_object* v_p_2607_){
_start:
{
lean_object* v___f_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___f_2608_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2608_, 0, v_p_2607_);
v___x_2609_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2610_ = l_Lean_PersistentArray_anyM___redArg(v___x_2609_, v_a_2606_, v___f_2608_);
v___x_2611_ = lean_unbox(v___x_2610_);
lean_dec(v___x_2610_);
if (v___x_2611_ == 0)
{
uint8_t v___x_2612_; 
v___x_2612_ = 1;
return v___x_2612_;
}
else
{
uint8_t v___x_2613_; 
v___x_2613_ = 0;
return v___x_2613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___boxed(lean_object* v_a_2614_, lean_object* v_p_2615_){
_start:
{
uint8_t v_res_2616_; lean_object* v_r_2617_; 
v_res_2616_ = l_Lean_PersistentArray_all___redArg(v_a_2614_, v_p_2615_);
v_r_2617_ = lean_box(v_res_2616_);
return v_r_2617_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all(lean_object* v_00_u03b1_2618_, lean_object* v_a_2619_, lean_object* v_p_2620_){
_start:
{
lean_object* v___f_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; 
v___f_2621_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2621_, 0, v_p_2620_);
v___x_2622_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2623_ = l_Lean_PersistentArray_anyM___redArg(v___x_2622_, v_a_2619_, v___f_2621_);
v___x_2624_ = lean_unbox(v___x_2623_);
lean_dec(v___x_2623_);
if (v___x_2624_ == 0)
{
uint8_t v___x_2625_; 
v___x_2625_ = 1;
return v___x_2625_;
}
else
{
uint8_t v___x_2626_; 
v___x_2626_ = 0;
return v___x_2626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___boxed(lean_object* v_00_u03b1_2627_, lean_object* v_a_2628_, lean_object* v_p_2629_){
_start:
{
uint8_t v_res_2630_; lean_object* v_r_2631_; 
v_res_2630_ = l_Lean_PersistentArray_all(v_00_u03b1_2627_, v_a_2628_, v_p_2629_);
v_r_2631_ = lean_box(v_res_2630_);
return v_r_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__0(lean_object* v_cs_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v_cs_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__2(lean_object* v_vs_2634_){
_start:
{
lean_object* v___x_2635_; 
v___x_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2635_, 0, v_vs_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg(lean_object* v_inst_2638_, lean_object* v_f_2639_, lean_object* v_x_2640_){
_start:
{
if (lean_obj_tag(v_x_2640_) == 0)
{
lean_object* v_toApplicative_2641_; lean_object* v_toFunctor_2642_; lean_object* v_cs_2643_; lean_object* v_map_2644_; lean_object* v___f_2645_; lean_object* v___f_2646_; size_t v_sz_2647_; size_t v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
v_toApplicative_2641_ = lean_ctor_get(v_inst_2638_, 0);
v_toFunctor_2642_ = lean_ctor_get(v_toApplicative_2641_, 0);
v_cs_2643_ = lean_ctor_get(v_x_2640_, 0);
lean_inc_ref(v_cs_2643_);
lean_dec_ref_known(v_x_2640_, 1);
v_map_2644_ = lean_ctor_get(v_toFunctor_2642_, 0);
lean_inc(v_map_2644_);
v___f_2645_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__0));
lean_inc_ref(v_inst_2638_);
v___f_2646_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapMAux___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2646_, 0, v_inst_2638_);
lean_closure_set(v___f_2646_, 1, v_f_2639_);
v_sz_2647_ = lean_array_size(v_cs_2643_);
v___x_2648_ = ((size_t)0ULL);
v___x_2649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2638_, v___f_2646_, v_sz_2647_, v___x_2648_, v_cs_2643_);
v___x_2650_ = lean_apply_4(v_map_2644_, lean_box(0), lean_box(0), v___f_2645_, v___x_2649_);
return v___x_2650_;
}
else
{
lean_object* v_toApplicative_2651_; lean_object* v_toFunctor_2652_; lean_object* v_vs_2653_; lean_object* v_map_2654_; lean_object* v___f_2655_; size_t v_sz_2656_; size_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_toApplicative_2651_ = lean_ctor_get(v_inst_2638_, 0);
v_toFunctor_2652_ = lean_ctor_get(v_toApplicative_2651_, 0);
v_vs_2653_ = lean_ctor_get(v_x_2640_, 0);
lean_inc_ref(v_vs_2653_);
lean_dec_ref_known(v_x_2640_, 1);
v_map_2654_ = lean_ctor_get(v_toFunctor_2652_, 0);
lean_inc(v_map_2654_);
v___f_2655_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__1));
v_sz_2656_ = lean_array_size(v_vs_2653_);
v___x_2657_ = ((size_t)0ULL);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2638_, v_f_2639_, v_sz_2656_, v___x_2657_, v_vs_2653_);
v___x_2659_ = lean_apply_4(v_map_2654_, lean_box(0), lean_box(0), v___f_2655_, v___x_2658_);
return v___x_2659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__1(lean_object* v_inst_2660_, lean_object* v_f_2661_, lean_object* v_c_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2660_, v_f_2661_, v_c_2662_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux(lean_object* v_00_u03b1_2664_, lean_object* v_m_2665_, lean_object* v_inst_2666_, lean_object* v_00_u03b2_2667_, lean_object* v_f_2668_, lean_object* v_x_2669_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2666_, v_f_2668_, v_x_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0(lean_object* v_root_2671_, lean_object* v_size_2672_, size_t v_shift_2673_, lean_object* v_tailOff_2674_, lean_object* v_toPure_2675_, lean_object* v_tail_2676_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2677_, 0, v_root_2671_);
lean_ctor_set(v___x_2677_, 1, v_tail_2676_);
lean_ctor_set(v___x_2677_, 2, v_size_2672_);
lean_ctor_set(v___x_2677_, 3, v_tailOff_2674_);
lean_ctor_set_usize(v___x_2677_, 4, v_shift_2673_);
v___x_2678_ = lean_apply_2(v_toPure_2675_, lean_box(0), v___x_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(lean_object* v_root_2679_, lean_object* v_size_2680_, lean_object* v_shift_2681_, lean_object* v_tailOff_2682_, lean_object* v_toPure_2683_, lean_object* v_tail_2684_){
_start:
{
size_t v_shift_boxed_2685_; lean_object* v_res_2686_; 
v_shift_boxed_2685_ = lean_unbox_usize(v_shift_2681_);
lean_dec(v_shift_2681_);
v_res_2686_ = l_Lean_PersistentArray_mapM___redArg___lam__0(v_root_2679_, v_size_2680_, v_shift_boxed_2685_, v_tailOff_2682_, v_toPure_2683_, v_tail_2684_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1(lean_object* v_size_2687_, size_t v_shift_2688_, lean_object* v_tailOff_2689_, lean_object* v_toPure_2690_, lean_object* v_tail_2691_, lean_object* v_inst_2692_, lean_object* v_f_2693_, lean_object* v_toBind_2694_, lean_object* v_root_2695_){
_start:
{
lean_object* v___x_2696_; lean_object* v___f_2697_; size_t v_sz_2698_; size_t v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2696_ = lean_box_usize(v_shift_2688_);
v___f_2697_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2697_, 0, v_root_2695_);
lean_closure_set(v___f_2697_, 1, v_size_2687_);
lean_closure_set(v___f_2697_, 2, v___x_2696_);
lean_closure_set(v___f_2697_, 3, v_tailOff_2689_);
lean_closure_set(v___f_2697_, 4, v_toPure_2690_);
v_sz_2698_ = lean_array_size(v_tail_2691_);
v___x_2699_ = ((size_t)0ULL);
v___x_2700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2692_, v_f_2693_, v_sz_2698_, v___x_2699_, v_tail_2691_);
v___x_2701_ = lean_apply_4(v_toBind_2694_, lean_box(0), lean_box(0), v___x_2700_, v___f_2697_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(lean_object* v_size_2702_, lean_object* v_shift_2703_, lean_object* v_tailOff_2704_, lean_object* v_toPure_2705_, lean_object* v_tail_2706_, lean_object* v_inst_2707_, lean_object* v_f_2708_, lean_object* v_toBind_2709_, lean_object* v_root_2710_){
_start:
{
size_t v_shift_boxed_2711_; lean_object* v_res_2712_; 
v_shift_boxed_2711_ = lean_unbox_usize(v_shift_2703_);
lean_dec(v_shift_2703_);
v_res_2712_ = l_Lean_PersistentArray_mapM___redArg___lam__1(v_size_2702_, v_shift_boxed_2711_, v_tailOff_2704_, v_toPure_2705_, v_tail_2706_, v_inst_2707_, v_f_2708_, v_toBind_2709_, v_root_2710_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object* v_inst_2713_, lean_object* v_f_2714_, lean_object* v_t_2715_){
_start:
{
lean_object* v_toApplicative_2716_; lean_object* v_toBind_2717_; lean_object* v_root_2718_; lean_object* v_tail_2719_; lean_object* v_size_2720_; size_t v_shift_2721_; lean_object* v_tailOff_2722_; lean_object* v_toPure_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___f_2726_; lean_object* v___x_2727_; 
v_toApplicative_2716_ = lean_ctor_get(v_inst_2713_, 0);
v_toBind_2717_ = lean_ctor_get(v_inst_2713_, 1);
lean_inc_n(v_toBind_2717_, 2);
v_root_2718_ = lean_ctor_get(v_t_2715_, 0);
lean_inc_ref(v_root_2718_);
v_tail_2719_ = lean_ctor_get(v_t_2715_, 1);
lean_inc_ref(v_tail_2719_);
v_size_2720_ = lean_ctor_get(v_t_2715_, 2);
lean_inc(v_size_2720_);
v_shift_2721_ = lean_ctor_get_usize(v_t_2715_, 4);
v_tailOff_2722_ = lean_ctor_get(v_t_2715_, 3);
lean_inc(v_tailOff_2722_);
lean_dec_ref(v_t_2715_);
v_toPure_2723_ = lean_ctor_get(v_toApplicative_2716_, 1);
lean_inc(v_toPure_2723_);
lean_inc(v_f_2714_);
lean_inc_ref(v_inst_2713_);
v___x_2724_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2713_, v_f_2714_, v_root_2718_);
v___x_2725_ = lean_box_usize(v_shift_2721_);
v___f_2726_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2726_, 0, v_size_2720_);
lean_closure_set(v___f_2726_, 1, v___x_2725_);
lean_closure_set(v___f_2726_, 2, v_tailOff_2722_);
lean_closure_set(v___f_2726_, 3, v_toPure_2723_);
lean_closure_set(v___f_2726_, 4, v_tail_2719_);
lean_closure_set(v___f_2726_, 5, v_inst_2713_);
lean_closure_set(v___f_2726_, 6, v_f_2714_);
lean_closure_set(v___f_2726_, 7, v_toBind_2717_);
v___x_2727_ = lean_apply_4(v_toBind_2717_, lean_box(0), lean_box(0), v___x_2724_, v___f_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM(lean_object* v_00_u03b1_2728_, lean_object* v_m_2729_, lean_object* v_inst_2730_, lean_object* v_00_u03b2_2731_, lean_object* v_f_2732_, lean_object* v_t_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Lean_PersistentArray_mapM___redArg(v_inst_2730_, v_f_2732_, v_t_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg___lam__0(lean_object* v_f_2735_, lean_object* v_x_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_apply_1(v_f_2735_, v_x_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg(lean_object* v_f_2738_, lean_object* v_t_2739_){
_start:
{
lean_object* v___f_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___f_2740_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2740_, 0, v_f_2738_);
v___x_2741_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2742_ = l_Lean_PersistentArray_mapM___redArg(v___x_2741_, v___f_2740_, v_t_2739_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map(lean_object* v_00_u03b1_2743_, lean_object* v_00_u03b2_2744_, lean_object* v_f_2745_, lean_object* v_t_2746_){
_start:
{
lean_object* v___f_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___f_2747_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2747_, 0, v_f_2745_);
v___x_2748_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2749_ = l_Lean_PersistentArray_mapM___redArg(v___x_2748_, v___f_2747_, v_t_2746_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg(lean_object* v_x_2750_, lean_object* v_x_2751_, lean_object* v_x_2752_){
_start:
{
if (lean_obj_tag(v_x_2750_) == 0)
{
lean_object* v_cs_2753_; lean_object* v_numNodes_2754_; lean_object* v_depth_2755_; lean_object* v_tailSize_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2778_; 
v_cs_2753_ = lean_ctor_get(v_x_2750_, 0);
v_numNodes_2754_ = lean_ctor_get(v_x_2751_, 0);
v_depth_2755_ = lean_ctor_get(v_x_2751_, 1);
v_tailSize_2756_ = lean_ctor_get(v_x_2751_, 2);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_x_2751_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2758_ = v_x_2751_;
v_isShared_2759_ = v_isSharedCheck_2778_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_tailSize_2756_);
lean_inc(v_depth_2755_);
lean_inc(v_numNodes_2754_);
lean_dec(v_x_2751_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2778_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___y_2763_; uint8_t v___x_2777_; 
v___x_2760_ = lean_unsigned_to_nat(1u);
v___x_2761_ = lean_nat_add(v_numNodes_2754_, v___x_2760_);
lean_dec(v_numNodes_2754_);
v___x_2777_ = lean_nat_dec_le(v_x_2752_, v_depth_2755_);
if (v___x_2777_ == 0)
{
lean_dec(v_depth_2755_);
lean_inc(v_x_2752_);
v___y_2763_ = v_x_2752_;
goto v___jp_2762_;
}
else
{
v___y_2763_ = v_depth_2755_;
goto v___jp_2762_;
}
v___jp_2762_:
{
lean_object* v___x_2765_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 1, v___y_2763_);
lean_ctor_set(v___x_2758_, 0, v___x_2761_);
v___x_2765_ = v___x_2758_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v___y_2763_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v_tailSize_2756_);
v___x_2765_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2766_ = lean_unsigned_to_nat(0u);
v___x_2767_ = lean_array_get_size(v_cs_2753_);
v___x_2768_ = lean_nat_dec_lt(v___x_2766_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_dec(v_x_2752_);
return v___x_2765_;
}
else
{
uint8_t v___x_2769_; 
v___x_2769_ = lean_nat_dec_le(v___x_2767_, v___x_2767_);
if (v___x_2769_ == 0)
{
if (v___x_2768_ == 0)
{
lean_dec(v_x_2752_);
return v___x_2765_;
}
else
{
size_t v___x_2770_; size_t v___x_2771_; lean_object* v___x_2772_; 
v___x_2770_ = ((size_t)0ULL);
v___x_2771_ = lean_usize_of_nat(v___x_2767_);
v___x_2772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2752_, v_cs_2753_, v___x_2770_, v___x_2771_, v___x_2765_);
lean_dec(v_x_2752_);
return v___x_2772_;
}
}
else
{
size_t v___x_2773_; size_t v___x_2774_; lean_object* v___x_2775_; 
v___x_2773_ = ((size_t)0ULL);
v___x_2774_ = lean_usize_of_nat(v___x_2767_);
v___x_2775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2752_, v_cs_2753_, v___x_2773_, v___x_2774_, v___x_2765_);
lean_dec(v_x_2752_);
return v___x_2775_;
}
}
}
}
}
}
else
{
lean_object* v_numNodes_2779_; lean_object* v_depth_2780_; lean_object* v_tailSize_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2794_; 
v_numNodes_2779_ = lean_ctor_get(v_x_2751_, 0);
v_depth_2780_ = lean_ctor_get(v_x_2751_, 1);
v_tailSize_2781_ = lean_ctor_get(v_x_2751_, 2);
v_isSharedCheck_2794_ = !lean_is_exclusive(v_x_2751_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2783_ = v_x_2751_;
v_isShared_2784_ = v_isSharedCheck_2794_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_tailSize_2781_);
lean_inc(v_depth_2780_);
lean_inc(v_numNodes_2779_);
lean_dec(v_x_2751_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2794_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2785_ = lean_unsigned_to_nat(1u);
v___x_2786_ = lean_nat_add(v_numNodes_2779_, v___x_2785_);
lean_dec(v_numNodes_2779_);
v___x_2787_ = lean_nat_dec_le(v_x_2752_, v_depth_2780_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2789_; 
lean_dec(v_depth_2780_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 1, v_x_2752_);
lean_ctor_set(v___x_2783_, 0, v___x_2786_);
v___x_2789_ = v___x_2783_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_x_2752_);
lean_ctor_set(v_reuseFailAlloc_2790_, 2, v_tailSize_2781_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
else
{
lean_object* v___x_2792_; 
lean_dec(v_x_2752_);
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v___x_2786_);
v___x_2792_ = v___x_2783_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_depth_2780_);
lean_ctor_set(v_reuseFailAlloc_2793_, 2, v_tailSize_2781_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(lean_object* v_x_2795_, lean_object* v_as_2796_, size_t v_i_2797_, size_t v_stop_2798_, lean_object* v_b_2799_){
_start:
{
uint8_t v___x_2800_; 
v___x_2800_ = lean_usize_dec_eq(v_i_2797_, v_stop_2798_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; size_t v___x_2805_; size_t v___x_2806_; 
v___x_2801_ = lean_array_uget_borrowed(v_as_2796_, v_i_2797_);
v___x_2802_ = lean_unsigned_to_nat(1u);
v___x_2803_ = lean_nat_add(v_x_2795_, v___x_2802_);
v___x_2804_ = l_Lean_PersistentArray_collectStats___redArg(v___x_2801_, v_b_2799_, v___x_2803_);
v___x_2805_ = ((size_t)1ULL);
v___x_2806_ = lean_usize_add(v_i_2797_, v___x_2805_);
v_i_2797_ = v___x_2806_;
v_b_2799_ = v___x_2804_;
goto _start;
}
else
{
return v_b_2799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg___boxed(lean_object* v_x_2808_, lean_object* v_as_2809_, lean_object* v_i_2810_, lean_object* v_stop_2811_, lean_object* v_b_2812_){
_start:
{
size_t v_i_boxed_2813_; size_t v_stop_boxed_2814_; lean_object* v_res_2815_; 
v_i_boxed_2813_ = lean_unbox_usize(v_i_2810_);
lean_dec(v_i_2810_);
v_stop_boxed_2814_ = lean_unbox_usize(v_stop_2811_);
lean_dec(v_stop_2811_);
v_res_2815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2808_, v_as_2809_, v_i_boxed_2813_, v_stop_boxed_2814_, v_b_2812_);
lean_dec_ref(v_as_2809_);
lean_dec(v_x_2808_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg___boxed(lean_object* v_x_2816_, lean_object* v_x_2817_, lean_object* v_x_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2816_, v_x_2817_, v_x_2818_);
lean_dec_ref(v_x_2816_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats(lean_object* v_00_u03b1_2820_, lean_object* v_x_2821_, lean_object* v_x_2822_, lean_object* v_x_2823_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2821_, v_x_2822_, v_x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___boxed(lean_object* v_00_u03b1_2825_, lean_object* v_x_2826_, lean_object* v_x_2827_, lean_object* v_x_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_PersistentArray_collectStats(v_00_u03b1_2825_, v_x_2826_, v_x_2827_, v_x_2828_);
lean_dec_ref(v_x_2826_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(lean_object* v_00_u03b1_2830_, lean_object* v_x_2831_, lean_object* v_as_2832_, size_t v_i_2833_, size_t v_stop_2834_, lean_object* v_b_2835_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2831_, v_as_2832_, v_i_2833_, v_stop_2834_, v_b_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2837_, lean_object* v_x_2838_, lean_object* v_as_2839_, lean_object* v_i_2840_, lean_object* v_stop_2841_, lean_object* v_b_2842_){
_start:
{
size_t v_i_boxed_2843_; size_t v_stop_boxed_2844_; lean_object* v_res_2845_; 
v_i_boxed_2843_ = lean_unbox_usize(v_i_2840_);
lean_dec(v_i_2840_);
v_stop_boxed_2844_ = lean_unbox_usize(v_stop_2841_);
lean_dec(v_stop_2841_);
v_res_2845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(v_00_u03b1_2837_, v_x_2838_, v_as_2839_, v_i_boxed_2843_, v_stop_boxed_2844_, v_b_2842_);
lean_dec_ref(v_as_2839_);
lean_dec(v_x_2838_);
return v_res_2845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg(lean_object* v_r_2846_){
_start:
{
lean_object* v_root_2847_; lean_object* v_tail_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_root_2847_ = lean_ctor_get(v_r_2846_, 0);
v_tail_2848_ = lean_ctor_get(v_r_2846_, 1);
v___x_2849_ = lean_unsigned_to_nat(0u);
v___x_2850_ = lean_array_get_size(v_tail_2848_);
v___x_2851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2849_);
lean_ctor_set(v___x_2851_, 2, v___x_2850_);
v___x_2852_ = l_Lean_PersistentArray_collectStats___redArg(v_root_2847_, v___x_2851_, v___x_2849_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg___boxed(lean_object* v_r_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l_Lean_PersistentArray_stats___redArg(v_r_2853_);
lean_dec_ref(v_r_2853_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats(lean_object* v_00_u03b1_2855_, lean_object* v_r_2856_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l_Lean_PersistentArray_stats___redArg(v_r_2856_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___boxed(lean_object* v_00_u03b1_2858_, lean_object* v_r_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_PersistentArray_stats(v_00_u03b1_2858_, v_r_2859_);
lean_dec_ref(v_r_2859_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Stats_toString(lean_object* v_s_2865_){
_start:
{
lean_object* v_numNodes_2866_; lean_object* v_depth_2867_; lean_object* v_tailSize_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v_numNodes_2866_ = lean_ctor_get(v_s_2865_, 0);
lean_inc(v_numNodes_2866_);
v_depth_2867_ = lean_ctor_get(v_s_2865_, 1);
lean_inc(v_depth_2867_);
v_tailSize_2868_ = lean_ctor_get(v_s_2865_, 2);
lean_inc(v_tailSize_2868_);
lean_dec_ref(v_s_2865_);
v___x_2869_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__0));
v___x_2870_ = l_Nat_reprFast(v_numNodes_2866_);
v___x_2871_ = lean_string_append(v___x_2869_, v___x_2870_);
lean_dec_ref(v___x_2870_);
v___x_2872_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__1));
v___x_2873_ = lean_string_append(v___x_2871_, v___x_2872_);
v___x_2874_ = l_Nat_reprFast(v_depth_2867_);
v___x_2875_ = lean_string_append(v___x_2873_, v___x_2874_);
lean_dec_ref(v___x_2874_);
v___x_2876_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__2));
v___x_2877_ = lean_string_append(v___x_2875_, v___x_2876_);
v___x_2878_ = l_Nat_reprFast(v_tailSize_2868_);
v___x_2879_ = lean_string_append(v___x_2877_, v___x_2878_);
lean_dec_ref(v___x_2878_);
v___x_2880_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__3));
v___x_2881_ = lean_string_append(v___x_2879_, v___x_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(lean_object* v_v_2884_, lean_object* v_j_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_zero_2887_; uint8_t v_isZero_2888_; 
v_zero_2887_ = lean_unsigned_to_nat(0u);
v_isZero_2888_ = lean_nat_dec_eq(v_j_2885_, v_zero_2887_);
if (v_isZero_2888_ == 1)
{
lean_dec(v_j_2885_);
lean_dec(v_v_2884_);
return v_a_2886_;
}
else
{
lean_object* v_one_2889_; lean_object* v_n_2890_; lean_object* v___x_2891_; 
v_one_2889_ = lean_unsigned_to_nat(1u);
v_n_2890_ = lean_nat_sub(v_j_2885_, v_one_2889_);
lean_dec(v_j_2885_);
lean_inc(v_v_2884_);
v___x_2891_ = l_Lean_PersistentArray_push___redArg(v_a_2886_, v_v_2884_);
v_j_2885_ = v_n_2890_;
v_a_2886_ = v___x_2891_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray___redArg(lean_object* v_n_2893_, lean_object* v_v_2894_){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
v___x_2896_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2894_, v_n_2893_, v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray(lean_object* v_00_u03b1_2897_, lean_object* v_n_2898_, lean_object* v_v_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_mkPersistentArray___redArg(v_n_2898_, v_v_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(lean_object* v_00_u03b1_2901_, lean_object* v_v_2902_, lean_object* v_n_2903_, lean_object* v_j_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2902_, v_j_2904_, v_a_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(lean_object* v_00_u03b1_2908_, lean_object* v_v_2909_, lean_object* v_n_2910_, lean_object* v_j_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(v_00_u03b1_2908_, v_v_2909_, v_n_2910_, v_j_2911_, v_a_2912_, v_a_2913_);
lean_dec(v_n_2910_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray___redArg(lean_object* v_n_2915_, lean_object* v_v_2916_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_mkPersistentArray___redArg(v_n_2915_, v_v_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray(lean_object* v_00_u03b1_2918_, lean_object* v_n_2919_, lean_object* v_v_2920_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_mkPersistentArray___redArg(v_n_2919_, v_v_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(lean_object* v_a_2922_, lean_object* v_a_2923_){
_start:
{
if (lean_obj_tag(v_a_2922_) == 0)
{
return v_a_2923_;
}
else
{
lean_object* v_head_2924_; lean_object* v_tail_2925_; lean_object* v___x_2926_; 
v_head_2924_ = lean_ctor_get(v_a_2922_, 0);
lean_inc(v_head_2924_);
v_tail_2925_ = lean_ctor_get(v_a_2922_, 1);
lean_inc(v_tail_2925_);
lean_dec_ref_known(v_a_2922_, 2);
v___x_2926_ = l_Lean_PersistentArray_push___redArg(v_a_2923_, v_head_2924_);
v_a_2922_ = v_tail_2925_;
v_a_2923_ = v___x_2926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop(lean_object* v_00_u03b1_2928_, lean_object* v_a_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_a_2929_, v_a_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27___redArg(lean_object* v_xs_2932_){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2933_ = lean_unsigned_to_nat(32u);
v___x_2934_ = lean_mk_empty_array_with_capacity(v___x_2933_);
lean_dec_ref(v___x_2934_);
v___x_2935_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___redArg___closed__1, &l_Lean_instInhabitedPersistentArray_default___redArg___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___redArg___closed__1);
v___x_2936_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_xs_2932_, v___x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27(lean_object* v_00_u03b1_2937_, lean_object* v_xs_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_List_toPArray_x27___redArg(v_xs_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object* v_xs_2940_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v___x_2941_ = lean_obj_once(&l_Lean_PersistentArray_empty___closed__0, &l_Lean_PersistentArray_empty___closed__0_once, _init_l_Lean_PersistentArray_empty___closed__0);
v___x_2942_ = lean_unsigned_to_nat(0u);
v___x_2943_ = lean_array_get_size(v_xs_2940_);
v___x_2944_ = lean_nat_dec_lt(v___x_2942_, v___x_2943_);
if (v___x_2944_ == 0)
{
return v___x_2941_;
}
else
{
uint8_t v___x_2945_; 
v___x_2945_ = lean_nat_dec_le(v___x_2943_, v___x_2943_);
if (v___x_2945_ == 0)
{
if (v___x_2944_ == 0)
{
return v___x_2941_;
}
else
{
size_t v___x_2946_; size_t v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = ((size_t)0ULL);
v___x_2947_ = lean_usize_of_nat(v___x_2943_);
v___x_2948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_2940_, v___x_2946_, v___x_2947_, v___x_2941_);
return v___x_2948_;
}
}
else
{
size_t v___x_2949_; size_t v___x_2950_; lean_object* v___x_2951_; 
v___x_2949_ = ((size_t)0ULL);
v___x_2950_ = lean_usize_of_nat(v___x_2943_);
v___x_2951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_2940_, v___x_2949_, v___x_2950_, v___x_2941_);
return v___x_2951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg___boxed(lean_object* v_xs_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_Lean_Array_toPArray_x27___redArg(v_xs_2952_);
lean_dec_ref(v_xs_2952_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27(lean_object* v_00_u03b1_2954_, lean_object* v_xs_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Array_toPArray_x27___redArg(v_xs_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___boxed(lean_object* v_00_u03b1_2957_, lean_object* v_xs_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_Array_toPArray_x27(v_00_u03b1_2957_, v_xs_2958_);
lean_dec_ref(v_xs_2958_);
return v_res_2959_;
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
