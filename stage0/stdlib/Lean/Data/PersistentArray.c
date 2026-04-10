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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_node_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_node_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_leaf_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_leaf_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedPersistentArrayNode_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedPersistentArrayNode_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedPersistentArrayNode_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedPersistentArrayNode_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedPersistentArrayNode_default___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedPersistentArrayNode_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedPersistentArrayNode_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedPersistentArrayNode___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedPersistentArrayNode___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArrayNode_isNode___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArrayNode_isNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___boxed(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Lean_PersistentArray_initShift;
LEAN_EXPORT size_t l_Lean_PersistentArray_branching;
static lean_once_cell_t l_Lean_instInhabitedPersistentArray_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedPersistentArray_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedPersistentArray_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedPersistentArray_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedPersistentArray___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedPersistentArray___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentArray_mkNewPath___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_mkNewPath___redArg___closed__0;
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
static lean_once_cell_t l_Lean_PersistentArray_mkNewTail___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_mkNewTail___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentArray_tooBig___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_tooBig___closed__0;
static lean_once_cell_t l_Lean_PersistentArray_tooBig___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_tooBig___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_tooBig;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_object*);
static lean_once_cell_t l_Lean_PersistentArray_popLeaf___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_popLeaf___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentArray_popLeaf___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_popLeaf___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_PersistentArray_instAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentArray_append___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_PersistentArray_instAppend___closed__0 = (const lean_object*)&l_Lean_PersistentArray_instAppend___closed__0_value;
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
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_mkPersistentArray___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkPersistentArray___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toPArray_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_toPArray_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toPArray_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_toPArray_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_toPArray_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toPArray_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___redArg___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_PersistentArrayNode_ctorIdx___redArg(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx(lean_object* v_00_u03b1_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_PersistentArrayNode_ctorIdx___redArg(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorIdx___boxed(lean_object* v_00_u03b1_9_, lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_PersistentArrayNode_ctorIdx(v_00_u03b1_9_, v_x_10_);
lean_dec_ref(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim___redArg(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_cs_14_; lean_object* v___x_15_; 
v_cs_14_ = lean_ctor_get(v_t_12_, 0);
lean_inc_ref(v_cs_14_);
lean_dec_ref(v_t_12_);
v___x_15_ = lean_apply_1(v_k_13_, v_cs_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim(lean_object* v_00_u03b1_16_, lean_object* v_motive__1_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_19_, v_k_21_);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_ctorElim___boxed(lean_object* v_00_u03b1_23_, lean_object* v_motive__1_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_PersistentArrayNode_ctorElim(v_00_u03b1_23_, v_motive__1_24_, v_ctorIdx_25_, v_t_26_, v_h_27_, v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_node_elim___redArg(lean_object* v_t_30_, lean_object* v_node_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_30_, v_node_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_node_elim(lean_object* v_00_u03b1_33_, lean_object* v_motive__1_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_node_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_35_, v_node_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_leaf_elim___redArg(lean_object* v_t_39_, lean_object* v_leaf_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_39_, v_leaf_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_leaf_elim(lean_object* v_00_u03b1_42_, lean_object* v_motive__1_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_leaf_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_PersistentArrayNode_ctorElim___redArg(v_t_44_, v_leaf_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object* v_00_u03b1_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = ((lean_object*)(l_Lean_instInhabitedPersistentArrayNode_default___closed__1));
return v___x_53_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArrayNode___closed__0(void){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArrayNode(lean_object* v_a_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
return v___x_56_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArrayNode_isNode___redArg(lean_object* v_x_57_){
_start:
{
if (lean_obj_tag(v_x_57_) == 0)
{
uint8_t v___x_58_; 
v___x_58_ = 1;
return v___x_58_;
}
else
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___redArg___boxed(lean_object* v_x_60_){
_start:
{
uint8_t v_res_61_; lean_object* v_r_62_; 
v_res_61_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_60_);
lean_dec_ref(v_x_60_);
v_r_62_ = lean_box(v_res_61_);
return v_r_62_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArrayNode_isNode(lean_object* v_00_u03b1_63_, lean_object* v_x_64_){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = l_Lean_PersistentArrayNode_isNode___redArg(v_x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArrayNode_isNode___boxed(lean_object* v_00_u03b1_66_, lean_object* v_x_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Lean_PersistentArrayNode_isNode(v_00_u03b1_66_, v_x_67_);
lean_dec_ref(v_x_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
static size_t _init_l_Lean_PersistentArray_initShift(void){
_start:
{
size_t v___x_70_; 
v___x_70_ = ((size_t)5ULL);
return v___x_70_;
}
}
static size_t _init_l_Lean_PersistentArray_branching(void){
_start:
{
size_t v___x_71_; 
v___x_71_ = ((size_t)32ULL);
return v___x_71_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___closed__0(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_unsigned_to_nat(32u);
v___x_73_ = lean_mk_empty_array_with_capacity(v___x_72_);
v___x_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray_default___closed__1(void){
_start:
{
size_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_75_ = ((size_t)5ULL);
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_unsigned_to_nat(32u);
v___x_78_ = lean_mk_empty_array_with_capacity(v___x_77_);
v___x_79_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__0, &l_Lean_instInhabitedPersistentArray_default___closed__0_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__0);
v___x_80_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
lean_ctor_set(v___x_80_, 2, v___x_76_);
lean_ctor_set(v___x_80_, 3, v___x_76_);
lean_ctor_set_usize(v___x_80_, 4, v___x_75_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object* v_00_u03b1_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_instInhabitedPersistentArray___closed__0(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPersistentArray(lean_object* v_a_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray___closed__0, &l_Lean_instInhabitedPersistentArray___closed__0_once, _init_l_Lean_instInhabitedPersistentArray___closed__0);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_empty(lean_object* v_00_u03b1_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_unsigned_to_nat(32u);
v___x_88_ = lean_mk_empty_array_with_capacity(v___x_87_);
lean_dec_ref(v___x_88_);
v___x_89_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
return v___x_89_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty___redArg(lean_object* v_a_90_){
_start:
{
lean_object* v_size_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v_size_91_ = lean_ctor_get(v_a_90_, 2);
v___x_92_ = lean_unsigned_to_nat(0u);
v___x_93_ = lean_nat_dec_eq(v_size_91_, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___redArg___boxed(lean_object* v_a_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_94_);
lean_dec_ref(v_a_94_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_isEmpty(lean_object* v_00_u03b1_97_, lean_object* v_a_98_){
_start:
{
uint8_t v___x_99_; 
v___x_99_ = l_Lean_PersistentArray_isEmpty___redArg(v_a_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_isEmpty___boxed(lean_object* v_00_u03b1_100_, lean_object* v_a_101_){
_start:
{
uint8_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = l_Lean_PersistentArray_isEmpty(v_00_u03b1_100_, v_a_101_);
lean_dec_ref(v_a_101_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkEmptyArray(lean_object* v_00_u03b1_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(32u);
v___x_106_ = lean_mk_empty_array_with_capacity(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_mul2Shift(size_t v_i_107_, size_t v_shift_108_){
_start:
{
size_t v___x_109_; 
v___x_109_ = lean_usize_shift_left(v_i_107_, v_shift_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mul2Shift___boxed(lean_object* v_i_110_, lean_object* v_shift_111_){
_start:
{
size_t v_i_boxed_112_; size_t v_shift_boxed_113_; size_t v_res_114_; lean_object* v_r_115_; 
v_i_boxed_112_ = lean_unbox_usize(v_i_110_);
lean_dec(v_i_110_);
v_shift_boxed_113_ = lean_unbox_usize(v_shift_111_);
lean_dec(v_shift_111_);
v_res_114_ = l_Lean_PersistentArray_mul2Shift(v_i_boxed_112_, v_shift_boxed_113_);
v_r_115_ = lean_box_usize(v_res_114_);
return v_r_115_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_div2Shift(size_t v_i_116_, size_t v_shift_117_){
_start:
{
size_t v___x_118_; 
v___x_118_ = lean_usize_shift_right(v_i_116_, v_shift_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_div2Shift___boxed(lean_object* v_i_119_, lean_object* v_shift_120_){
_start:
{
size_t v_i_boxed_121_; size_t v_shift_boxed_122_; size_t v_res_123_; lean_object* v_r_124_; 
v_i_boxed_121_ = lean_unbox_usize(v_i_119_);
lean_dec(v_i_119_);
v_shift_boxed_122_ = lean_unbox_usize(v_shift_120_);
lean_dec(v_shift_120_);
v_res_123_ = l_Lean_PersistentArray_div2Shift(v_i_boxed_121_, v_shift_boxed_122_);
v_r_124_ = lean_box_usize(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT size_t l_Lean_PersistentArray_mod2Shift(size_t v_i_125_, size_t v_shift_126_){
_start:
{
size_t v___x_127_; size_t v___x_128_; size_t v___x_129_; size_t v___x_130_; 
v___x_127_ = ((size_t)1ULL);
v___x_128_ = lean_usize_shift_left(v___x_127_, v_shift_126_);
v___x_129_ = lean_usize_sub(v___x_128_, v___x_127_);
v___x_130_ = lean_usize_land(v_i_125_, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mod2Shift___boxed(lean_object* v_i_131_, lean_object* v_shift_132_){
_start:
{
size_t v_i_boxed_133_; size_t v_shift_boxed_134_; size_t v_res_135_; lean_object* v_r_136_; 
v_i_boxed_133_ = lean_unbox_usize(v_i_131_);
lean_dec(v_i_131_);
v_shift_boxed_134_ = lean_unbox_usize(v_shift_132_);
lean_dec(v_shift_132_);
v_res_135_ = l_Lean_PersistentArray_mod2Shift(v_i_boxed_133_, v_shift_boxed_134_);
v_r_136_ = lean_box_usize(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___redArg(lean_object* v_inst_137_, lean_object* v_x_138_, size_t v_x_139_, size_t v_x_140_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_cs_141_; lean_object* v___x_142_; size_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; size_t v___x_150_; size_t v___x_151_; 
v_cs_141_ = lean_ctor_get(v_x_138_, 0);
v___x_142_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_143_ = lean_usize_shift_right(v_x_139_, v_x_140_);
v___x_144_ = lean_usize_to_nat(v___x_143_);
v___x_145_ = lean_array_get_borrowed(v___x_142_, v_cs_141_, v___x_144_);
lean_dec(v___x_144_);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_shift_left(v___x_146_, v_x_140_);
v___x_148_ = lean_usize_sub(v___x_147_, v___x_146_);
v___x_149_ = lean_usize_land(v_x_139_, v___x_148_);
v___x_150_ = ((size_t)5ULL);
v___x_151_ = lean_usize_sub(v_x_140_, v___x_150_);
v_x_138_ = v___x_145_;
v_x_139_ = v___x_149_;
v_x_140_ = v___x_151_;
goto _start;
}
else
{
lean_object* v_vs_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_vs_153_ = lean_ctor_get(v_x_138_, 0);
v___x_154_ = lean_usize_to_nat(v_x_139_);
v___x_155_ = lean_array_get_borrowed(v_inst_137_, v_vs_153_, v___x_154_);
lean_dec(v___x_154_);
lean_inc(v___x_155_);
return v___x_155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___redArg___boxed(lean_object* v_inst_156_, lean_object* v_x_157_, lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
size_t v_x_92__boxed_160_; size_t v_x_93__boxed_161_; lean_object* v_res_162_; 
v_x_92__boxed_160_ = lean_unbox_usize(v_x_158_);
lean_dec(v_x_158_);
v_x_93__boxed_161_ = lean_unbox_usize(v_x_159_);
lean_dec(v_x_159_);
v_res_162_ = l_Lean_PersistentArray_getAux___redArg(v_inst_156_, v_x_157_, v_x_92__boxed_160_, v_x_93__boxed_161_);
lean_dec_ref(v_x_157_);
lean_dec(v_inst_156_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux(lean_object* v_00_u03b1_163_, lean_object* v_inst_164_, lean_object* v_x_165_, size_t v_x_166_, size_t v_x_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_PersistentArray_getAux___redArg(v_inst_164_, v_x_165_, v_x_166_, v_x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_getAux___boxed(lean_object* v_00_u03b1_169_, lean_object* v_inst_170_, lean_object* v_x_171_, lean_object* v_x_172_, lean_object* v_x_173_){
_start:
{
size_t v_x_134__boxed_174_; size_t v_x_135__boxed_175_; lean_object* v_res_176_; 
v_x_134__boxed_174_ = lean_unbox_usize(v_x_172_);
lean_dec(v_x_172_);
v_x_135__boxed_175_ = lean_unbox_usize(v_x_173_);
lean_dec(v_x_173_);
v_res_176_ = l_Lean_PersistentArray_getAux(v_00_u03b1_169_, v_inst_170_, v_x_171_, v_x_134__boxed_174_, v_x_135__boxed_175_);
lean_dec_ref(v_x_171_);
lean_dec(v_inst_170_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object* v_inst_177_, lean_object* v_t_178_, lean_object* v_i_179_){
_start:
{
lean_object* v_root_180_; lean_object* v_tail_181_; size_t v_shift_182_; lean_object* v_tailOff_183_; uint8_t v___x_184_; 
v_root_180_ = lean_ctor_get(v_t_178_, 0);
v_tail_181_ = lean_ctor_get(v_t_178_, 1);
v_shift_182_ = lean_ctor_get_usize(v_t_178_, 4);
v_tailOff_183_ = lean_ctor_get(v_t_178_, 3);
v___x_184_ = lean_nat_dec_le(v_tailOff_183_, v_i_179_);
if (v___x_184_ == 0)
{
size_t v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_usize_of_nat(v_i_179_);
v___x_186_ = l_Lean_PersistentArray_getAux___redArg(v_inst_177_, v_root_180_, v___x_185_, v_shift_182_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_nat_sub(v_i_179_, v_tailOff_183_);
v___x_188_ = lean_array_get_borrowed(v_inst_177_, v_tail_181_, v___x_187_);
lean_dec(v___x_187_);
lean_inc(v___x_188_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___redArg___boxed(lean_object* v_inst_189_, lean_object* v_t_190_, lean_object* v_i_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_189_, v_t_190_, v_i_191_);
lean_dec(v_i_191_);
lean_dec_ref(v_t_190_);
lean_dec(v_inst_189_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21(lean_object* v_00_u03b1_193_, lean_object* v_inst_194_, lean_object* v_t_195_, lean_object* v_i_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_194_, v_t_195_, v_i_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_get_x21___boxed(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_, lean_object* v_t_200_, lean_object* v_i_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_PersistentArray_get_x21(v_00_u03b1_198_, v_inst_199_, v_t_200_, v_i_201_);
lean_dec(v_i_201_);
lean_dec_ref(v_t_200_);
lean_dec(v_inst_199_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(lean_object* v_inst_203_, lean_object* v_xs_204_, lean_object* v_i_205_, lean_object* v_x_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_PersistentArray_get_x21___redArg(v_inst_203_, v_xs_204_, v_i_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed(lean_object* v_inst_208_, lean_object* v_xs_209_, lean_object* v_i_210_, lean_object* v_x_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0(v_inst_208_, v_xs_209_, v_i_210_, v_x_211_);
lean_dec(v_i_210_);
lean_dec_ref(v_xs_209_);
lean_dec(v_inst_208_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg(lean_object* v_inst_213_){
_start:
{
lean_object* v___f_214_; 
v___f_214_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_214_, 0, v_inst_213_);
return v___f_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited(lean_object* v_00_u03b1_215_, lean_object* v_inst_216_){
_start:
{
lean_object* v___f_217_; 
v___f_217_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_instGetElemNatLtSizeOfInhabited___redArg___lam__0___boxed), 4, 1);
lean_closure_set(v___f_217_, 0, v_inst_216_);
return v___f_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___redArg(lean_object* v_x_218_, size_t v_x_219_, size_t v_x_220_, lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_object* v_cs_222_; size_t v_j_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_cs_222_ = lean_ctor_get(v_x_218_, 0);
v_j_223_ = lean_usize_shift_right(v_x_219_, v_x_220_);
v___x_224_ = lean_usize_to_nat(v_j_223_);
v___x_225_ = lean_array_get_size(v_cs_222_);
v___x_226_ = lean_nat_dec_lt(v___x_224_, v___x_225_);
if (v___x_226_ == 0)
{
lean_dec(v___x_224_);
lean_dec(v_x_221_);
return v_x_218_;
}
else
{
lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_244_; 
lean_inc_ref(v_cs_222_);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_x_218_, 0);
lean_dec(v_unused_245_);
v___x_228_ = v_x_218_;
v_isShared_229_ = v_isSharedCheck_244_;
goto v_resetjp_227_;
}
else
{
lean_dec(v_x_218_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_244_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
size_t v___x_230_; size_t v___x_231_; size_t v___x_232_; size_t v_i_233_; size_t v___x_234_; size_t v_shift_235_; lean_object* v_v_236_; lean_object* v___x_237_; lean_object* v_xs_x27_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_shift_left(v___x_230_, v_x_220_);
v___x_232_ = lean_usize_sub(v___x_231_, v___x_230_);
v_i_233_ = lean_usize_land(v_x_219_, v___x_232_);
v___x_234_ = ((size_t)5ULL);
v_shift_235_ = lean_usize_sub(v_x_220_, v___x_234_);
v_v_236_ = lean_array_fget(v_cs_222_, v___x_224_);
v___x_237_ = lean_box(0);
v_xs_x27_238_ = lean_array_fset(v_cs_222_, v___x_224_, v___x_237_);
v___x_239_ = l_Lean_PersistentArray_setAux___redArg(v_v_236_, v_i_233_, v_shift_235_, v_x_221_);
v___x_240_ = lean_array_fset(v_xs_x27_238_, v___x_224_, v___x_239_);
lean_dec(v___x_224_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_240_);
v___x_242_ = v___x_228_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_object* v_vs_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_255_; 
v_vs_246_ = lean_ctor_get(v_x_218_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_255_ == 0)
{
v___x_248_ = v_x_218_;
v_isShared_249_ = v_isSharedCheck_255_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_vs_246_);
lean_dec(v_x_218_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_255_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_250_ = lean_usize_to_nat(v_x_219_);
v___x_251_ = lean_array_set(v_vs_246_, v___x_250_, v_x_221_);
lean_dec(v___x_250_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_251_);
v___x_253_ = v___x_248_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___redArg___boxed(lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
size_t v_x_77__boxed_260_; size_t v_x_78__boxed_261_; lean_object* v_res_262_; 
v_x_77__boxed_260_ = lean_unbox_usize(v_x_257_);
lean_dec(v_x_257_);
v_x_78__boxed_261_ = lean_unbox_usize(v_x_258_);
lean_dec(v_x_258_);
v_res_262_ = l_Lean_PersistentArray_setAux___redArg(v_x_256_, v_x_77__boxed_260_, v_x_78__boxed_261_, v_x_259_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux(lean_object* v_00_u03b1_263_, lean_object* v_x_264_, size_t v_x_265_, size_t v_x_266_, lean_object* v_x_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_PersistentArray_setAux___redArg(v_x_264_, v_x_265_, v_x_266_, v_x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_setAux___boxed(lean_object* v_00_u03b1_269_, lean_object* v_x_270_, lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
size_t v_x_147__boxed_274_; size_t v_x_148__boxed_275_; lean_object* v_res_276_; 
v_x_147__boxed_274_ = lean_unbox_usize(v_x_271_);
lean_dec(v_x_271_);
v_x_148__boxed_275_ = lean_unbox_usize(v_x_272_);
lean_dec(v_x_272_);
v_res_276_ = l_Lean_PersistentArray_setAux(v_00_u03b1_269_, v_x_270_, v_x_147__boxed_274_, v_x_148__boxed_275_, v_x_273_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg(lean_object* v_t_277_, lean_object* v_i_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_root_280_; lean_object* v_tail_281_; lean_object* v_size_282_; size_t v_shift_283_; lean_object* v_tailOff_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_299_; 
v_root_280_ = lean_ctor_get(v_t_277_, 0);
v_tail_281_ = lean_ctor_get(v_t_277_, 1);
v_size_282_ = lean_ctor_get(v_t_277_, 2);
v_shift_283_ = lean_ctor_get_usize(v_t_277_, 4);
v_tailOff_284_ = lean_ctor_get(v_t_277_, 3);
v_isSharedCheck_299_ = !lean_is_exclusive(v_t_277_);
if (v_isSharedCheck_299_ == 0)
{
v___x_286_ = v_t_277_;
v_isShared_287_ = v_isSharedCheck_299_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_tailOff_284_);
lean_inc(v_size_282_);
lean_inc(v_tail_281_);
lean_inc(v_root_280_);
lean_dec(v_t_277_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_299_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
uint8_t v___x_288_; 
v___x_288_ = lean_nat_dec_le(v_tailOff_284_, v_i_278_);
if (v___x_288_ == 0)
{
size_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_289_ = lean_usize_of_nat(v_i_278_);
v___x_290_ = l_Lean_PersistentArray_setAux___redArg(v_root_280_, v___x_289_, v_shift_283_, v_a_279_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_290_);
v___x_292_ = v___x_286_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v_tail_281_);
lean_ctor_set(v_reuseFailAlloc_293_, 2, v_size_282_);
lean_ctor_set(v_reuseFailAlloc_293_, 3, v_tailOff_284_);
lean_ctor_set_usize(v_reuseFailAlloc_293_, 4, v_shift_283_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_294_ = lean_nat_sub(v_i_278_, v_tailOff_284_);
v___x_295_ = lean_array_set(v_tail_281_, v___x_294_, v_a_279_);
lean_dec(v___x_294_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 1, v___x_295_);
v___x_297_ = v___x_286_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_root_280_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_size_282_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_tailOff_284_);
lean_ctor_set_usize(v_reuseFailAlloc_298_, 4, v_shift_283_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___redArg___boxed(lean_object* v_t_300_, lean_object* v_i_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_PersistentArray_set___redArg(v_t_300_, v_i_301_, v_a_302_);
lean_dec(v_i_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set(lean_object* v_00_u03b1_304_, lean_object* v_t_305_, lean_object* v_i_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_PersistentArray_set___redArg(v_t_305_, v_i_306_, v_a_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_set___boxed(lean_object* v_00_u03b1_309_, lean_object* v_t_310_, lean_object* v_i_311_, lean_object* v_a_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_PersistentArray_set(v_00_u03b1_309_, v_t_310_, v_i_311_, v_a_312_);
lean_dec(v_i_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___redArg(lean_object* v_f_314_, lean_object* v_x_315_, size_t v_x_316_, size_t v_x_317_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
lean_object* v_cs_318_; size_t v_j_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_cs_318_ = lean_ctor_get(v_x_315_, 0);
v_j_319_ = lean_usize_shift_right(v_x_316_, v_x_317_);
v___x_320_ = lean_usize_to_nat(v_j_319_);
v___x_321_ = lean_array_get_size(v_cs_318_);
v___x_322_ = lean_nat_dec_lt(v___x_320_, v___x_321_);
if (v___x_322_ == 0)
{
lean_dec(v___x_320_);
lean_dec(v_f_314_);
return v_x_315_;
}
else
{
lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_340_; 
lean_inc_ref(v_cs_318_);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_315_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; 
v_unused_341_ = lean_ctor_get(v_x_315_, 0);
lean_dec(v_unused_341_);
v___x_324_ = v_x_315_;
v_isShared_325_ = v_isSharedCheck_340_;
goto v_resetjp_323_;
}
else
{
lean_dec(v_x_315_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_340_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
size_t v___x_326_; size_t v___x_327_; size_t v___x_328_; size_t v_i_329_; size_t v___x_330_; size_t v_shift_331_; lean_object* v_v_332_; lean_object* v___x_333_; lean_object* v_xs_x27_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_shift_left(v___x_326_, v_x_317_);
v___x_328_ = lean_usize_sub(v___x_327_, v___x_326_);
v_i_329_ = lean_usize_land(v_x_316_, v___x_328_);
v___x_330_ = ((size_t)5ULL);
v_shift_331_ = lean_usize_sub(v_x_317_, v___x_330_);
v_v_332_ = lean_array_fget(v_cs_318_, v___x_320_);
v___x_333_ = lean_box(0);
v_xs_x27_334_ = lean_array_fset(v_cs_318_, v___x_320_, v___x_333_);
v___x_335_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_314_, v_v_332_, v_i_329_, v_shift_331_);
v___x_336_ = lean_array_fset(v_xs_x27_334_, v___x_320_, v___x_335_);
lean_dec(v___x_320_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 0, v___x_336_);
v___x_338_ = v___x_324_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_336_);
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
else
{
lean_object* v_vs_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_vs_342_ = lean_ctor_get(v_x_315_, 0);
v___x_343_ = lean_usize_to_nat(v_x_316_);
v___x_344_ = lean_array_get_size(v_vs_342_);
v___x_345_ = lean_nat_dec_lt(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
lean_dec(v___x_343_);
lean_dec(v_f_314_);
return v_x_315_;
}
else
{
lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_357_; 
lean_inc_ref(v_vs_342_);
v_isSharedCheck_357_ = !lean_is_exclusive(v_x_315_);
if (v_isSharedCheck_357_ == 0)
{
lean_object* v_unused_358_; 
v_unused_358_ = lean_ctor_get(v_x_315_, 0);
lean_dec(v_unused_358_);
v___x_347_ = v_x_315_;
v_isShared_348_ = v_isSharedCheck_357_;
goto v_resetjp_346_;
}
else
{
lean_dec(v_x_315_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_357_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v_v_349_; lean_object* v___x_350_; lean_object* v_xs_x27_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v_v_349_ = lean_array_fget(v_vs_342_, v___x_343_);
v___x_350_ = lean_box(0);
v_xs_x27_351_ = lean_array_fset(v_vs_342_, v___x_343_, v___x_350_);
v___x_352_ = lean_apply_1(v_f_314_, v_v_349_);
v___x_353_ = lean_array_fset(v_xs_x27_351_, v___x_343_, v___x_352_);
lean_dec(v___x_343_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_353_);
v___x_355_ = v___x_347_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___redArg___boxed(lean_object* v_f_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_){
_start:
{
size_t v_x_92__boxed_363_; size_t v_x_93__boxed_364_; lean_object* v_res_365_; 
v_x_92__boxed_363_ = lean_unbox_usize(v_x_361_);
lean_dec(v_x_361_);
v_x_93__boxed_364_ = lean_unbox_usize(v_x_362_);
lean_dec(v_x_362_);
v_res_365_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_359_, v_x_360_, v_x_92__boxed_363_, v_x_93__boxed_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux(lean_object* v_00_u03b1_366_, lean_object* v_inst_367_, lean_object* v_f_368_, lean_object* v_x_369_, size_t v_x_370_, size_t v_x_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_368_, v_x_369_, v_x_370_, v_x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___boxed(lean_object* v_00_u03b1_373_, lean_object* v_inst_374_, lean_object* v_f_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
size_t v_x_170__boxed_379_; size_t v_x_171__boxed_380_; lean_object* v_res_381_; 
v_x_170__boxed_379_ = lean_unbox_usize(v_x_377_);
lean_dec(v_x_377_);
v_x_171__boxed_380_ = lean_unbox_usize(v_x_378_);
lean_dec(v_x_378_);
v_res_381_ = l_Lean_PersistentArray_modifyAux(v_00_u03b1_373_, v_inst_374_, v_f_375_, v_x_376_, v_x_170__boxed_379_, v_x_171__boxed_380_);
lean_dec(v_inst_374_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg(lean_object* v_t_382_, lean_object* v_i_383_, lean_object* v_f_384_){
_start:
{
lean_object* v_root_385_; lean_object* v_tail_386_; lean_object* v_size_387_; size_t v_shift_388_; lean_object* v_tailOff_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_413_; 
v_root_385_ = lean_ctor_get(v_t_382_, 0);
v_tail_386_ = lean_ctor_get(v_t_382_, 1);
v_size_387_ = lean_ctor_get(v_t_382_, 2);
v_shift_388_ = lean_ctor_get_usize(v_t_382_, 4);
v_tailOff_389_ = lean_ctor_get(v_t_382_, 3);
v_isSharedCheck_413_ = !lean_is_exclusive(v_t_382_);
if (v_isSharedCheck_413_ == 0)
{
v___x_391_ = v_t_382_;
v_isShared_392_ = v_isSharedCheck_413_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_tailOff_389_);
lean_inc(v_size_387_);
lean_inc(v_tail_386_);
lean_inc(v_root_385_);
lean_dec(v_t_382_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_413_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
uint8_t v___x_393_; 
v___x_393_ = lean_nat_dec_le(v_tailOff_389_, v_i_383_);
if (v___x_393_ == 0)
{
size_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_394_ = lean_usize_of_nat(v_i_383_);
v___x_395_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_384_, v_root_385_, v___x_394_, v_shift_388_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v___x_395_);
v___x_397_ = v___x_391_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_tail_386_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_size_387_);
lean_ctor_set(v_reuseFailAlloc_398_, 3, v_tailOff_389_);
lean_ctor_set_usize(v_reuseFailAlloc_398_, 4, v_shift_388_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_399_ = lean_nat_sub(v_i_383_, v_tailOff_389_);
v___x_400_ = lean_array_get_size(v_tail_386_);
v___x_401_ = lean_nat_dec_lt(v___x_399_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_403_; 
lean_dec(v___x_399_);
lean_dec(v_f_384_);
if (v_isShared_392_ == 0)
{
v___x_403_ = v___x_391_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_root_385_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_tail_386_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_size_387_);
lean_ctor_set(v_reuseFailAlloc_404_, 3, v_tailOff_389_);
lean_ctor_set_usize(v_reuseFailAlloc_404_, 4, v_shift_388_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
else
{
lean_object* v_v_405_; lean_object* v___x_406_; lean_object* v_xs_x27_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_411_; 
v_v_405_ = lean_array_fget(v_tail_386_, v___x_399_);
v___x_406_ = lean_box(0);
v_xs_x27_407_ = lean_array_fset(v_tail_386_, v___x_399_, v___x_406_);
v___x_408_ = lean_apply_1(v_f_384_, v_v_405_);
v___x_409_ = lean_array_fset(v_xs_x27_407_, v___x_399_, v___x_408_);
lean_dec(v___x_399_);
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 1, v___x_409_);
v___x_411_ = v___x_391_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_root_385_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_409_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_size_387_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_tailOff_389_);
lean_ctor_set_usize(v_reuseFailAlloc_412_, 4, v_shift_388_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___redArg___boxed(lean_object* v_t_414_, lean_object* v_i_415_, lean_object* v_f_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_PersistentArray_modify___redArg(v_t_414_, v_i_415_, v_f_416_);
lean_dec(v_i_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify(lean_object* v_00_u03b1_418_, lean_object* v_inst_419_, lean_object* v_t_420_, lean_object* v_i_421_, lean_object* v_f_422_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_PersistentArray_modify___redArg(v_t_420_, v_i_421_, v_f_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___boxed(lean_object* v_00_u03b1_424_, lean_object* v_inst_425_, lean_object* v_t_426_, lean_object* v_i_427_, lean_object* v_f_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_PersistentArray_modify(v_00_u03b1_424_, v_inst_425_, v_t_426_, v_i_427_, v_f_428_);
lean_dec(v_i_427_);
lean_dec(v_inst_425_);
return v_res_429_;
}
}
static lean_object* _init_l_Lean_PersistentArray_mkNewPath___redArg___closed__0(void){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_PersistentArray_mkEmptyArray(lean_box(0));
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___redArg(size_t v_shift_431_, lean_object* v_a_432_){
_start:
{
size_t v___x_433_; uint8_t v___x_434_; 
v___x_433_ = ((size_t)0ULL);
v___x_434_ = lean_usize_dec_eq(v_shift_431_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; size_t v___x_436_; size_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_435_ = lean_obj_once(&l_Lean_PersistentArray_mkNewPath___redArg___closed__0, &l_Lean_PersistentArray_mkNewPath___redArg___closed__0_once, _init_l_Lean_PersistentArray_mkNewPath___redArg___closed__0);
v___x_436_ = ((size_t)5ULL);
v___x_437_ = lean_usize_sub(v_shift_431_, v___x_436_);
v___x_438_ = l_Lean_PersistentArray_mkNewPath___redArg(v___x_437_, v_a_432_);
v___x_439_ = lean_array_push(v___x_435_, v___x_438_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v_a_432_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___redArg___boxed(lean_object* v_shift_442_, lean_object* v_a_443_){
_start:
{
size_t v_shift_boxed_444_; lean_object* v_res_445_; 
v_shift_boxed_444_ = lean_unbox_usize(v_shift_442_);
lean_dec(v_shift_442_);
v_res_445_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_boxed_444_, v_a_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath(lean_object* v_00_u03b1_446_, size_t v_shift_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_447_, v_a_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewPath___boxed(lean_object* v_00_u03b1_450_, lean_object* v_shift_451_, lean_object* v_a_452_){
_start:
{
size_t v_shift_boxed_453_; lean_object* v_res_454_; 
v_shift_boxed_453_ = lean_unbox_usize(v_shift_451_);
lean_dec(v_shift_451_);
v_res_454_ = l_Lean_PersistentArray_mkNewPath(v_00_u03b1_450_, v_shift_boxed_453_, v_a_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg(lean_object* v_x_455_, size_t v_x_456_, size_t v_x_457_, lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_455_) == 0)
{
lean_object* v_cs_459_; size_t v___x_460_; uint8_t v___x_461_; 
v_cs_459_ = lean_ctor_get(v_x_455_, 0);
v___x_460_ = ((size_t)32ULL);
v___x_461_ = lean_usize_dec_lt(v_x_456_, v___x_460_);
if (v___x_461_ == 0)
{
size_t v_j_462_; size_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v_shift_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_j_462_ = lean_usize_shift_right(v_x_456_, v_x_457_);
v___x_463_ = ((size_t)1ULL);
v___x_464_ = lean_usize_shift_left(v___x_463_, v_x_457_);
v___x_465_ = ((size_t)5ULL);
v_shift_466_ = lean_usize_sub(v_x_457_, v___x_465_);
v___x_467_ = lean_usize_to_nat(v_j_462_);
v___x_468_ = lean_array_get_size(v_cs_459_);
v___x_469_ = lean_nat_dec_lt(v___x_467_, v___x_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_478_; 
lean_inc_ref(v_cs_459_);
lean_dec(v___x_467_);
v_isSharedCheck_478_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_478_ == 0)
{
lean_object* v_unused_479_; 
v_unused_479_ = lean_ctor_get(v_x_455_, 0);
lean_dec(v_unused_479_);
v___x_471_ = v_x_455_;
v_isShared_472_ = v_isSharedCheck_478_;
goto v_resetjp_470_;
}
else
{
lean_dec(v_x_455_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_478_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_473_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_466_, v_x_458_);
v___x_474_ = lean_array_push(v_cs_459_, v___x_473_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_474_);
v___x_476_ = v___x_471_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
else
{
if (v___x_469_ == 0)
{
lean_dec(v___x_467_);
lean_dec_ref(v_x_458_);
return v_x_455_;
}
else
{
lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_493_; 
lean_inc_ref(v_cs_459_);
v_isSharedCheck_493_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_493_ == 0)
{
lean_object* v_unused_494_; 
v_unused_494_ = lean_ctor_get(v_x_455_, 0);
lean_dec(v_unused_494_);
v___x_481_ = v_x_455_;
v_isShared_482_ = v_isSharedCheck_493_;
goto v_resetjp_480_;
}
else
{
lean_dec(v_x_455_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_493_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
size_t v___x_483_; size_t v_i_484_; lean_object* v_v_485_; lean_object* v___x_486_; lean_object* v_xs_x27_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_483_ = lean_usize_sub(v___x_464_, v___x_463_);
v_i_484_ = lean_usize_land(v_x_456_, v___x_483_);
v_v_485_ = lean_array_fget(v_cs_459_, v___x_467_);
v___x_486_ = lean_box(0);
v_xs_x27_487_ = lean_array_fset(v_cs_459_, v___x_467_, v___x_486_);
v___x_488_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_v_485_, v_i_484_, v_shift_466_, v_x_458_);
v___x_489_ = lean_array_fset(v_xs_x27_487_, v___x_467_, v___x_488_);
lean_dec(v___x_467_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_489_);
v___x_491_ = v___x_481_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
else
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_503_; 
lean_inc_ref(v_cs_459_);
v_isSharedCheck_503_ = !lean_is_exclusive(v_x_455_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v_x_455_, 0);
lean_dec(v_unused_504_);
v___x_496_ = v_x_455_;
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_x_455_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
lean_ctor_set_tag(v___x_496_, 1);
lean_ctor_set(v___x_496_, 0, v_x_458_);
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_x_458_);
v___x_499_ = v_reuseFailAlloc_502_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_array_push(v_cs_459_, v___x_499_);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
}
}
else
{
lean_dec_ref(v_x_458_);
return v_x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___redArg___boxed(lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
size_t v_x_107__boxed_509_; size_t v_x_108__boxed_510_; lean_object* v_res_511_; 
v_x_107__boxed_509_ = lean_unbox_usize(v_x_506_);
lean_dec(v_x_506_);
v_x_108__boxed_510_ = lean_unbox_usize(v_x_507_);
lean_dec(v_x_507_);
v_res_511_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_505_, v_x_107__boxed_509_, v_x_108__boxed_510_, v_x_508_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf(lean_object* v_00_u03b1_512_, lean_object* v_x_513_, size_t v_x_514_, size_t v_x_515_, lean_object* v_x_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_513_, v_x_514_, v_x_515_, v_x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_insertNewLeaf___boxed(lean_object* v_00_u03b1_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
size_t v_x_201__boxed_523_; size_t v_x_202__boxed_524_; lean_object* v_res_525_; 
v_x_201__boxed_523_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_x_202__boxed_524_ = lean_unbox_usize(v_x_521_);
lean_dec(v_x_521_);
v_res_525_ = l_Lean_PersistentArray_insertNewLeaf(v_00_u03b1_518_, v_x_519_, v_x_201__boxed_523_, v_x_202__boxed_524_, v_x_522_);
return v_res_525_;
}
}
static lean_object* _init_l_Lean_PersistentArray_mkNewTail___redArg___closed__1(void){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_PersistentArray_mkEmptyArray(lean_box(0));
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail___redArg(lean_object* v_t_529_){
_start:
{
lean_object* v_root_530_; lean_object* v_tail_531_; lean_object* v_size_532_; size_t v_shift_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_560_; 
v_root_530_ = lean_ctor_get(v_t_529_, 0);
v_tail_531_ = lean_ctor_get(v_t_529_, 1);
v_size_532_ = lean_ctor_get(v_t_529_, 2);
v_shift_533_ = lean_ctor_get_usize(v_t_529_, 4);
v_isSharedCheck_560_ = !lean_is_exclusive(v_t_529_);
if (v_isSharedCheck_560_ == 0)
{
lean_object* v_unused_561_; 
v_unused_561_ = lean_ctor_get(v_t_529_, 3);
lean_dec(v_unused_561_);
v___x_535_ = v_t_529_;
v_isShared_536_ = v_isSharedCheck_560_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_size_532_);
lean_inc(v_tail_531_);
lean_inc(v_root_530_);
lean_dec(v_t_529_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_560_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
size_t v___x_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_537_ = ((size_t)1ULL);
v___x_538_ = ((size_t)5ULL);
v___x_539_ = lean_usize_add(v_shift_533_, v___x_538_);
v___x_540_ = lean_usize_shift_left(v___x_537_, v___x_539_);
v___x_541_ = lean_usize_to_nat(v___x_540_);
v___x_542_ = lean_nat_dec_le(v_size_532_, v___x_541_);
lean_dec(v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v_n_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_543_ = lean_obj_once(&l_Lean_PersistentArray_mkNewPath___redArg___closed__0, &l_Lean_PersistentArray_mkNewPath___redArg___closed__0_once, _init_l_Lean_PersistentArray_mkNewPath___redArg___closed__0);
v_n_544_ = lean_array_push(v___x_543_, v_root_530_);
v___x_545_ = l_Lean_PersistentArray_mkNewPath___redArg(v_shift_533_, v_tail_531_);
v___x_546_ = lean_array_push(v_n_544_, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
v___x_548_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
lean_inc(v_size_532_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 3, v_size_532_);
lean_ctor_set(v___x_535_, 1, v___x_548_);
lean_ctor_set(v___x_535_, 0, v___x_547_);
v___x_550_ = v___x_535_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_547_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v___x_548_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_size_532_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_size_532_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_ctor_set_usize(v___x_550_, 4, v___x_539_);
return v___x_550_;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; size_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = lean_nat_sub(v_size_532_, v___x_552_);
v___x_554_ = lean_usize_of_nat(v___x_553_);
lean_dec(v___x_553_);
v___x_555_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_root_530_, v___x_554_, v_shift_533_, v_tail_531_);
v___x_556_ = lean_obj_once(&l_Lean_PersistentArray_mkNewTail___redArg___closed__1, &l_Lean_PersistentArray_mkNewTail___redArg___closed__1_once, _init_l_Lean_PersistentArray_mkNewTail___redArg___closed__1);
lean_inc(v_size_532_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 3, v_size_532_);
lean_ctor_set(v___x_535_, 1, v___x_556_);
lean_ctor_set(v___x_535_, 0, v___x_555_);
v___x_558_ = v___x_535_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_555_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_size_532_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_size_532_);
lean_ctor_set_usize(v_reuseFailAlloc_559_, 4, v_shift_533_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mkNewTail(lean_object* v_00_u03b1_562_, lean_object* v_t_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_PersistentArray_mkNewTail___redArg(v_t_563_);
return v___x_564_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__0(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = l_System_Platform_numBits;
v___x_566_ = lean_unsigned_to_nat(2u);
v___x_567_ = lean_nat_pow(v___x_566_, v___x_565_);
return v___x_567_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig___closed__1(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = lean_unsigned_to_nat(3u);
v___x_569_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__0, &l_Lean_PersistentArray_tooBig___closed__0_once, _init_l_Lean_PersistentArray_tooBig___closed__0);
v___x_570_ = lean_nat_shiftr(v___x_569_, v___x_568_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_PersistentArray_tooBig(void){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = lean_obj_once(&l_Lean_PersistentArray_tooBig___closed__1, &l_Lean_PersistentArray_tooBig___closed__1_once, _init_l_Lean_PersistentArray_tooBig___closed__1);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push___redArg(lean_object* v_t_572_, lean_object* v_a_573_){
_start:
{
lean_object* v_root_574_; lean_object* v_tail_575_; lean_object* v_size_576_; size_t v_shift_577_; lean_object* v_tailOff_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_596_; 
v_root_574_ = lean_ctor_get(v_t_572_, 0);
v_tail_575_ = lean_ctor_get(v_t_572_, 1);
v_size_576_ = lean_ctor_get(v_t_572_, 2);
v_shift_577_ = lean_ctor_get_usize(v_t_572_, 4);
v_tailOff_578_ = lean_ctor_get(v_t_572_, 3);
v_isSharedCheck_596_ = !lean_is_exclusive(v_t_572_);
if (v_isSharedCheck_596_ == 0)
{
v___x_580_ = v_t_572_;
v_isShared_581_ = v_isSharedCheck_596_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_tailOff_578_);
lean_inc(v_size_576_);
lean_inc(v_tail_575_);
lean_inc(v_root_574_);
lean_dec(v_t_572_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_596_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_r_586_; 
v___x_582_ = lean_array_push(v_tail_575_, v_a_573_);
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_add(v_size_576_, v___x_583_);
lean_inc_ref(v___x_582_);
if (v_isShared_581_ == 0)
{
lean_ctor_set(v___x_580_, 2, v___x_584_);
lean_ctor_set(v___x_580_, 1, v___x_582_);
v_r_586_ = v___x_580_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_root_574_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_tailOff_578_);
lean_ctor_set_usize(v_reuseFailAlloc_595_, 4, v_shift_577_);
v_r_586_ = v_reuseFailAlloc_595_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
uint8_t v___y_588_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_590_ = lean_array_get_size(v___x_582_);
lean_dec_ref(v___x_582_);
v___x_591_ = lean_unsigned_to_nat(32u);
v___x_592_ = lean_nat_dec_lt(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = l_Lean_PersistentArray_tooBig;
v___x_594_ = lean_nat_dec_le(v___x_593_, v_size_576_);
lean_dec(v_size_576_);
v___y_588_ = v___x_594_;
goto v___jp_587_;
}
else
{
lean_dec(v_size_576_);
v___y_588_ = v___x_592_;
goto v___jp_587_;
}
v___jp_587_:
{
if (v___y_588_ == 0)
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_PersistentArray_mkNewTail___redArg(v_r_586_);
return v___x_589_;
}
else
{
return v_r_586_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push(lean_object* v_00_u03b1_597_, lean_object* v_t_598_, lean_object* v_a_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_PersistentArray_push___redArg(v_t_598_, v_a_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_object* v_00_u03b1_601_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(32u);
v___x_603_ = lean_mk_empty_array_with_capacity(v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0(void){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_box(0));
return v___x_604_;
}
}
static lean_object* _init_l_Lean_PersistentArray_popLeaf___redArg___closed__1(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
v___x_606_ = lean_box(0);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf___redArg(lean_object* v_x_608_){
_start:
{
if (lean_obj_tag(v_x_608_) == 0)
{
lean_object* v_cs_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_659_; 
v_cs_609_ = lean_ctor_get(v_x_608_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v_x_608_);
if (v_isSharedCheck_659_ == 0)
{
v___x_611_ = v_x_608_;
v_isShared_612_ = v_isSharedCheck_659_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_cs_609_);
lean_dec(v_x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_659_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v___x_613_ = lean_array_get_size(v_cs_609_);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_nat_dec_eq(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v_idx_617_; lean_object* v_last_618_; lean_object* v___x_619_; lean_object* v_fst_620_; 
v___x_616_ = lean_unsigned_to_nat(1u);
v_idx_617_ = lean_nat_sub(v___x_613_, v___x_616_);
v_last_618_ = lean_array_fget_borrowed(v_cs_609_, v_idx_617_);
lean_inc(v_last_618_);
v___x_619_ = l_Lean_PersistentArray_popLeaf___redArg(v_last_618_);
v_fst_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_fst_620_);
if (lean_obj_tag(v_fst_620_) == 0)
{
lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_628_; 
lean_dec(v_idx_617_);
lean_del_object(v___x_611_);
lean_dec_ref(v_cs_609_);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; lean_object* v_unused_630_; 
v_unused_629_ = lean_ctor_get(v___x_619_, 1);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v___x_619_, 0);
lean_dec(v_unused_630_);
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
else
{
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_628_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_626_; 
v___x_624_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 1, v___x_624_);
v___x_626_ = v___x_622_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_fst_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
else
{
lean_object* v_snd_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_656_; 
v_snd_631_ = lean_ctor_get(v___x_619_, 1);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v___x_619_, 0);
lean_dec(v_unused_657_);
v___x_633_ = v___x_619_;
v_isShared_634_ = v_isSharedCheck_656_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_snd_631_);
lean_dec(v___x_619_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_656_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v_cs_x27_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_635_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v_cs_x27_636_ = lean_array_fset(v_cs_609_, v_idx_617_, v___x_635_);
v___x_637_ = lean_array_get_size(v_snd_631_);
v___x_638_ = lean_nat_dec_eq(v___x_637_, v___x_614_);
if (v___x_638_ == 0)
{
lean_object* v___x_640_; 
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 0, v_snd_631_);
v___x_640_ = v___x_611_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_snd_631_);
v___x_640_ = v_reuseFailAlloc_645_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = lean_array_fset(v_cs_x27_636_, v_idx_617_, v___x_640_);
lean_dec(v_idx_617_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_641_);
v___x_643_ = v___x_633_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_fst_620_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
else
{
lean_object* v_cs_x27_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
lean_dec(v_snd_631_);
lean_dec(v_idx_617_);
lean_del_object(v___x_611_);
v_cs_x27_646_ = lean_array_pop(v_cs_x27_636_);
v___x_647_ = lean_array_get_size(v_cs_x27_646_);
v___x_648_ = lean_nat_dec_eq(v___x_647_, v___x_614_);
if (v___x_648_ == 0)
{
lean_object* v___x_650_; 
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v_cs_x27_646_);
v___x_650_ = v___x_633_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_fst_620_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_cs_x27_646_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
else
{
lean_object* v___x_652_; lean_object* v___x_654_; 
lean_dec_ref(v_cs_x27_646_);
v___x_652_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 1, v___x_652_);
v___x_654_ = v___x_633_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_fst_620_);
lean_ctor_set(v_reuseFailAlloc_655_, 1, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
}
else
{
lean_object* v___x_658_; 
lean_del_object(v___x_611_);
lean_dec_ref(v_cs_609_);
v___x_658_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__1, &l_Lean_PersistentArray_popLeaf___redArg___closed__1_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__1);
return v___x_658_;
}
}
}
else
{
lean_object* v_vs_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_vs_660_ = lean_ctor_get(v_x_608_, 0);
lean_inc_ref(v_vs_660_);
lean_dec_ref(v_x_608_);
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v_vs_660_);
v___x_662_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_661_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf(lean_object* v_00_u03b1_664_, lean_object* v_x_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_PersistentArray_popLeaf___redArg(v_x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop___redArg(lean_object* v_t_667_){
_start:
{
lean_object* v_root_668_; lean_object* v_tail_669_; lean_object* v_size_670_; size_t v_shift_671_; lean_object* v_tailOff_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_root_668_ = lean_ctor_get(v_t_667_, 0);
v_tail_669_ = lean_ctor_get(v_t_667_, 1);
v_size_670_ = lean_ctor_get(v_t_667_, 2);
v_shift_671_ = lean_ctor_get_usize(v_t_667_, 4);
v_tailOff_672_ = lean_ctor_get(v_t_667_, 3);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_array_get_size(v_tail_669_);
v___x_675_ = lean_nat_dec_lt(v___x_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; lean_object* v_fst_677_; 
lean_inc_ref(v_root_668_);
v___x_676_ = l_Lean_PersistentArray_popLeaf___redArg(v_root_668_);
v_fst_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_fst_677_);
if (lean_obj_tag(v_fst_677_) == 0)
{
lean_dec_ref(v___x_676_);
return v_t_667_;
}
else
{
lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_710_; 
lean_inc(v_size_670_);
v_isSharedCheck_710_ = !lean_is_exclusive(v_t_667_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; lean_object* v_unused_712_; lean_object* v_unused_713_; lean_object* v_unused_714_; 
v_unused_711_ = lean_ctor_get(v_t_667_, 3);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_t_667_, 2);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_t_667_, 1);
lean_dec(v_unused_713_);
v_unused_714_ = lean_ctor_get(v_t_667_, 0);
lean_dec(v_unused_714_);
v___x_679_ = v_t_667_;
v_isShared_680_ = v_isSharedCheck_710_;
goto v_resetjp_678_;
}
else
{
lean_dec(v_t_667_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_710_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v_snd_681_; lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_709_; 
v_snd_681_ = lean_ctor_get(v___x_676_, 1);
lean_inc(v_snd_681_);
lean_dec_ref(v___x_676_);
v_val_682_ = lean_ctor_get(v_fst_677_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v_fst_677_);
if (v_isSharedCheck_709_ == 0)
{
v___x_684_ = v_fst_677_;
v_isShared_685_ = v_isSharedCheck_709_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_dec(v_fst_677_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_709_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v_last_686_; lean_object* v___x_687_; lean_object* v_newSize_688_; lean_object* v___x_689_; lean_object* v_newTailOff_690_; uint8_t v___y_692_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_last_686_ = lean_array_pop(v_val_682_);
v___x_687_ = lean_unsigned_to_nat(1u);
v_newSize_688_ = lean_nat_sub(v_size_670_, v___x_687_);
lean_dec(v_size_670_);
v___x_689_ = lean_array_get_size(v_last_686_);
v_newTailOff_690_ = lean_nat_sub(v_newSize_688_, v___x_689_);
v___x_705_ = lean_array_get_size(v_snd_681_);
v___x_706_ = lean_nat_dec_eq(v___x_705_, v___x_687_);
if (v___x_706_ == 0)
{
v___y_692_ = v___x_706_;
goto v___jp_691_;
}
else
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = lean_array_fget_borrowed(v_snd_681_, v___x_673_);
v___x_708_ = l_Lean_PersistentArrayNode_isNode___redArg(v___x_707_);
v___y_692_ = v___x_708_;
goto v___jp_691_;
}
v___jp_691_:
{
if (v___y_692_ == 0)
{
lean_object* v___x_694_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set_tag(v___x_684_, 0);
lean_ctor_set(v___x_684_, 0, v_snd_681_);
v___x_694_ = v___x_684_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_snd_681_);
v___x_694_ = v_reuseFailAlloc_698_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_696_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 3, v_newTailOff_690_);
lean_ctor_set(v___x_679_, 2, v_newSize_688_);
lean_ctor_set(v___x_679_, 1, v_last_686_);
lean_ctor_set(v___x_679_, 0, v___x_694_);
v___x_696_ = v___x_679_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_last_686_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_newSize_688_);
lean_ctor_set(v_reuseFailAlloc_697_, 3, v_newTailOff_690_);
lean_ctor_set_usize(v_reuseFailAlloc_697_, 4, v_shift_671_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
else
{
lean_object* v___x_699_; size_t v___x_700_; size_t v___x_701_; lean_object* v___x_703_; 
lean_del_object(v___x_684_);
v___x_699_ = lean_array_fget(v_snd_681_, v___x_673_);
lean_dec(v_snd_681_);
v___x_700_ = ((size_t)5ULL);
v___x_701_ = lean_usize_sub(v_shift_671_, v___x_700_);
if (v_isShared_680_ == 0)
{
lean_ctor_set(v___x_679_, 3, v_newTailOff_690_);
lean_ctor_set(v___x_679_, 2, v_newSize_688_);
lean_ctor_set(v___x_679_, 1, v_last_686_);
lean_ctor_set(v___x_679_, 0, v___x_699_);
v___x_703_ = v___x_679_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_last_686_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_newSize_688_);
lean_ctor_set(v_reuseFailAlloc_704_, 3, v_newTailOff_690_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_ctor_set_usize(v___x_703_, 4, v___x_701_);
return v___x_703_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_724_; 
lean_inc(v_tailOff_672_);
lean_inc(v_size_670_);
lean_inc_ref(v_tail_669_);
lean_inc_ref(v_root_668_);
v_isSharedCheck_724_ = !lean_is_exclusive(v_t_667_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; lean_object* v_unused_726_; lean_object* v_unused_727_; lean_object* v_unused_728_; 
v_unused_725_ = lean_ctor_get(v_t_667_, 3);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_t_667_, 2);
lean_dec(v_unused_726_);
v_unused_727_ = lean_ctor_get(v_t_667_, 1);
lean_dec(v_unused_727_);
v_unused_728_ = lean_ctor_get(v_t_667_, 0);
lean_dec(v_unused_728_);
v___x_716_ = v_t_667_;
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
else
{
lean_dec(v_t_667_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_718_ = lean_array_pop(v_tail_669_);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_sub(v_size_670_, v___x_719_);
lean_dec(v_size_670_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 2, v___x_720_);
lean_ctor_set(v___x_716_, 1, v___x_718_);
v___x_722_ = v___x_716_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_root_668_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_723_, 2, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_723_, 3, v_tailOff_672_);
lean_ctor_set_usize(v_reuseFailAlloc_723_, 4, v_shift_671_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop(lean_object* v_00_u03b1_729_, lean_object* v_t_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PersistentArray_pop___redArg(v_t_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(lean_object* v_inst_732_, lean_object* v_f_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
lean_object* v_cs_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_cs_736_ = lean_ctor_get(v_x_734_, 0);
lean_inc_ref(v_cs_736_);
lean_dec_ref(v_x_734_);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_array_get_size(v_cs_736_);
v___x_739_ = lean_nat_dec_lt(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v_toApplicative_740_; lean_object* v_toPure_741_; lean_object* v___x_742_; 
lean_dec_ref(v_cs_736_);
lean_dec(v_f_733_);
v_toApplicative_740_ = lean_ctor_get(v_inst_732_, 0);
lean_inc_ref(v_toApplicative_740_);
lean_dec_ref(v_inst_732_);
v_toPure_741_ = lean_ctor_get(v_toApplicative_740_, 1);
lean_inc(v_toPure_741_);
lean_dec_ref(v_toApplicative_740_);
v___x_742_ = lean_apply_2(v_toPure_741_, lean_box(0), v_x_735_);
return v___x_742_;
}
else
{
lean_object* v___f_743_; uint8_t v___x_744_; 
lean_inc_ref(v_inst_732_);
v___f_743_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_743_, 0, v_inst_732_);
lean_closure_set(v___f_743_, 1, v_f_733_);
v___x_744_ = lean_nat_dec_le(v___x_738_, v___x_738_);
if (v___x_744_ == 0)
{
if (v___x_739_ == 0)
{
lean_object* v_toApplicative_745_; lean_object* v_toPure_746_; lean_object* v___x_747_; 
lean_dec_ref(v___f_743_);
lean_dec_ref(v_cs_736_);
v_toApplicative_745_ = lean_ctor_get(v_inst_732_, 0);
lean_inc_ref(v_toApplicative_745_);
lean_dec_ref(v_inst_732_);
v_toPure_746_ = lean_ctor_get(v_toApplicative_745_, 1);
lean_inc(v_toPure_746_);
lean_dec_ref(v_toApplicative_745_);
v___x_747_ = lean_apply_2(v_toPure_746_, lean_box(0), v_x_735_);
return v___x_747_;
}
else
{
size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((size_t)0ULL);
v___x_749_ = lean_usize_of_nat(v___x_738_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_732_, v___f_743_, v_cs_736_, v___x_748_, v___x_749_, v_x_735_);
return v___x_750_;
}
}
else
{
size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((size_t)0ULL);
v___x_752_ = lean_usize_of_nat(v___x_738_);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_732_, v___f_743_, v_cs_736_, v___x_751_, v___x_752_, v_x_735_);
return v___x_753_;
}
}
}
else
{
lean_object* v_vs_754_; lean_object* v___x_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_vs_754_ = lean_ctor_get(v_x_734_, 0);
lean_inc_ref(v_vs_754_);
lean_dec_ref(v_x_734_);
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = lean_array_get_size(v_vs_754_);
v___x_757_ = lean_nat_dec_lt(v___x_755_, v___x_756_);
if (v___x_757_ == 0)
{
lean_object* v_toApplicative_758_; lean_object* v_toPure_759_; lean_object* v___x_760_; 
lean_dec_ref(v_vs_754_);
lean_dec(v_f_733_);
v_toApplicative_758_ = lean_ctor_get(v_inst_732_, 0);
lean_inc_ref(v_toApplicative_758_);
lean_dec_ref(v_inst_732_);
v_toPure_759_ = lean_ctor_get(v_toApplicative_758_, 1);
lean_inc(v_toPure_759_);
lean_dec_ref(v_toApplicative_758_);
v___x_760_ = lean_apply_2(v_toPure_759_, lean_box(0), v_x_735_);
return v___x_760_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = lean_nat_dec_le(v___x_756_, v___x_756_);
if (v___x_761_ == 0)
{
if (v___x_757_ == 0)
{
lean_object* v_toApplicative_762_; lean_object* v_toPure_763_; lean_object* v___x_764_; 
lean_dec_ref(v_vs_754_);
lean_dec(v_f_733_);
v_toApplicative_762_ = lean_ctor_get(v_inst_732_, 0);
lean_inc_ref(v_toApplicative_762_);
lean_dec_ref(v_inst_732_);
v_toPure_763_ = lean_ctor_get(v_toApplicative_762_, 1);
lean_inc(v_toPure_763_);
lean_dec_ref(v_toApplicative_762_);
v___x_764_ = lean_apply_2(v_toPure_763_, lean_box(0), v_x_735_);
return v___x_764_;
}
else
{
size_t v___x_765_; size_t v___x_766_; lean_object* v___x_767_; 
v___x_765_ = ((size_t)0ULL);
v___x_766_ = lean_usize_of_nat(v___x_756_);
v___x_767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_732_, v_f_733_, v_vs_754_, v___x_765_, v___x_766_, v_x_735_);
return v___x_767_;
}
}
else
{
size_t v___x_768_; size_t v___x_769_; lean_object* v___x_770_; 
v___x_768_ = ((size_t)0ULL);
v___x_769_ = lean_usize_of_nat(v___x_756_);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_732_, v_f_733_, v_vs_754_, v___x_768_, v___x_769_, v_x_735_);
return v___x_770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0(lean_object* v_inst_771_, lean_object* v_f_772_, lean_object* v_b_773_, lean_object* v_c_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_771_, v_f_772_, v_c_774_, v_b_773_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux(lean_object* v_00_u03b1_776_, lean_object* v_m_777_, lean_object* v_inst_778_, lean_object* v_00_u03b2_779_, lean_object* v_f_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_778_, v_f_780_, v_x_781_, v_x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(lean_object* v_j_784_, lean_object* v_cs_785_, lean_object* v_toApplicative_786_, lean_object* v_inst_787_, lean_object* v___f_788_, lean_object* v_b_789_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_add(v_j_784_, v___x_790_);
v___x_792_ = lean_array_get_size(v_cs_785_);
v___x_793_ = lean_nat_dec_lt(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v_toPure_794_; lean_object* v___x_795_; 
lean_dec(v___x_791_);
lean_dec(v___f_788_);
lean_dec_ref(v_inst_787_);
lean_dec_ref(v_cs_785_);
v_toPure_794_ = lean_ctor_get(v_toApplicative_786_, 1);
lean_inc(v_toPure_794_);
lean_dec_ref(v_toApplicative_786_);
v___x_795_ = lean_apply_2(v_toPure_794_, lean_box(0), v_b_789_);
return v___x_795_;
}
else
{
uint8_t v___x_796_; 
v___x_796_ = lean_nat_dec_le(v___x_792_, v___x_792_);
if (v___x_796_ == 0)
{
if (v___x_793_ == 0)
{
lean_object* v_toPure_797_; lean_object* v___x_798_; 
lean_dec(v___x_791_);
lean_dec(v___f_788_);
lean_dec_ref(v_inst_787_);
lean_dec_ref(v_cs_785_);
v_toPure_797_ = lean_ctor_get(v_toApplicative_786_, 1);
lean_inc(v_toPure_797_);
lean_dec_ref(v_toApplicative_786_);
v___x_798_ = lean_apply_2(v_toPure_797_, lean_box(0), v_b_789_);
return v___x_798_;
}
else
{
size_t v___x_799_; size_t v___x_800_; lean_object* v___x_801_; 
lean_dec_ref(v_toApplicative_786_);
v___x_799_ = lean_usize_of_nat(v___x_791_);
lean_dec(v___x_791_);
v___x_800_ = lean_usize_of_nat(v___x_792_);
v___x_801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_787_, v___f_788_, v_cs_785_, v___x_799_, v___x_800_, v_b_789_);
return v___x_801_;
}
}
else
{
size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
lean_dec_ref(v_toApplicative_786_);
v___x_802_ = lean_usize_of_nat(v___x_791_);
lean_dec(v___x_791_);
v___x_803_ = lean_usize_of_nat(v___x_792_);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_787_, v___f_788_, v_cs_785_, v___x_802_, v___x_803_, v_b_789_);
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed(lean_object* v_j_805_, lean_object* v_cs_806_, lean_object* v_toApplicative_807_, lean_object* v_inst_808_, lean_object* v___f_809_, lean_object* v_b_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(v_j_805_, v_cs_806_, v_toApplicative_807_, v_inst_808_, v___f_809_, v_b_810_);
lean_dec(v_j_805_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(lean_object* v_inst_812_, lean_object* v_f_813_, lean_object* v_x_814_, size_t v_x_815_, size_t v_x_816_, lean_object* v_x_817_){
_start:
{
if (lean_obj_tag(v_x_814_) == 0)
{
lean_object* v_toApplicative_818_; lean_object* v_toBind_819_; lean_object* v_cs_820_; lean_object* v___f_821_; lean_object* v___x_822_; size_t v___x_823_; lean_object* v_j_824_; lean_object* v___f_825_; lean_object* v___x_826_; size_t v___x_827_; size_t v___x_828_; size_t v___x_829_; size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_toApplicative_818_ = lean_ctor_get(v_inst_812_, 0);
v_toBind_819_ = lean_ctor_get(v_inst_812_, 1);
lean_inc(v_toBind_819_);
v_cs_820_ = lean_ctor_get(v_x_814_, 0);
lean_inc_ref_n(v_cs_820_, 2);
lean_dec_ref(v_x_814_);
lean_inc(v_f_813_);
lean_inc_ref_n(v_inst_812_, 2);
v___f_821_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_821_, 0, v_inst_812_);
lean_closure_set(v___f_821_, 1, v_f_813_);
v___x_822_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_823_ = lean_usize_shift_right(v_x_815_, v_x_816_);
v_j_824_ = lean_usize_to_nat(v___x_823_);
lean_inc_ref(v_toApplicative_818_);
lean_inc(v_j_824_);
v___f_825_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_825_, 0, v_j_824_);
lean_closure_set(v___f_825_, 1, v_cs_820_);
lean_closure_set(v___f_825_, 2, v_toApplicative_818_);
lean_closure_set(v___f_825_, 3, v_inst_812_);
lean_closure_set(v___f_825_, 4, v___f_821_);
v___x_826_ = lean_array_get(v___x_822_, v_cs_820_, v_j_824_);
lean_dec(v_j_824_);
lean_dec_ref(v_cs_820_);
v___x_827_ = ((size_t)1ULL);
v___x_828_ = lean_usize_shift_left(v___x_827_, v_x_816_);
v___x_829_ = lean_usize_sub(v___x_828_, v___x_827_);
v___x_830_ = lean_usize_land(v_x_815_, v___x_829_);
v___x_831_ = ((size_t)5ULL);
v___x_832_ = lean_usize_sub(v_x_816_, v___x_831_);
v___x_833_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_812_, v_f_813_, v___x_826_, v___x_830_, v___x_832_, v_x_817_);
v___x_834_ = lean_apply_4(v_toBind_819_, lean_box(0), lean_box(0), v___x_833_, v___f_825_);
return v___x_834_;
}
else
{
lean_object* v_toApplicative_835_; lean_object* v_vs_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_toApplicative_835_ = lean_ctor_get(v_inst_812_, 0);
v_vs_836_ = lean_ctor_get(v_x_814_, 0);
lean_inc_ref(v_vs_836_);
lean_dec_ref(v_x_814_);
v___x_837_ = lean_usize_to_nat(v_x_815_);
v___x_838_ = lean_array_get_size(v_vs_836_);
v___x_839_ = lean_nat_dec_lt(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v_toPure_840_; lean_object* v___x_841_; 
lean_inc_ref(v_toApplicative_835_);
lean_dec(v___x_837_);
lean_dec_ref(v_vs_836_);
lean_dec(v_f_813_);
lean_dec_ref(v_inst_812_);
v_toPure_840_ = lean_ctor_get(v_toApplicative_835_, 1);
lean_inc(v_toPure_840_);
lean_dec_ref(v_toApplicative_835_);
v___x_841_ = lean_apply_2(v_toPure_840_, lean_box(0), v_x_817_);
return v___x_841_;
}
else
{
uint8_t v___x_842_; 
v___x_842_ = lean_nat_dec_le(v___x_838_, v___x_838_);
if (v___x_842_ == 0)
{
if (v___x_839_ == 0)
{
lean_object* v_toPure_843_; lean_object* v___x_844_; 
lean_inc_ref(v_toApplicative_835_);
lean_dec(v___x_837_);
lean_dec_ref(v_vs_836_);
lean_dec(v_f_813_);
lean_dec_ref(v_inst_812_);
v_toPure_843_ = lean_ctor_get(v_toApplicative_835_, 1);
lean_inc(v_toPure_843_);
lean_dec_ref(v_toApplicative_835_);
v___x_844_ = lean_apply_2(v_toPure_843_, lean_box(0), v_x_817_);
return v___x_844_;
}
else
{
size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_usize_of_nat(v___x_837_);
lean_dec(v___x_837_);
v___x_846_ = lean_usize_of_nat(v___x_838_);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_812_, v_f_813_, v_vs_836_, v___x_845_, v___x_846_, v_x_817_);
return v___x_847_;
}
}
else
{
size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; 
v___x_848_ = lean_usize_of_nat(v___x_837_);
lean_dec(v___x_837_);
v___x_849_ = lean_usize_of_nat(v___x_838_);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_812_, v_f_813_, v_vs_836_, v___x_848_, v___x_849_, v_x_817_);
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___boxed(lean_object* v_inst_851_, lean_object* v_f_852_, lean_object* v_x_853_, lean_object* v_x_854_, lean_object* v_x_855_, lean_object* v_x_856_){
_start:
{
size_t v_x_215__boxed_857_; size_t v_x_216__boxed_858_; lean_object* v_res_859_; 
v_x_215__boxed_857_ = lean_unbox_usize(v_x_854_);
lean_dec(v_x_854_);
v_x_216__boxed_858_ = lean_unbox_usize(v_x_855_);
lean_dec(v_x_855_);
v_res_859_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_851_, v_f_852_, v_x_853_, v_x_215__boxed_857_, v_x_216__boxed_858_, v_x_856_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(lean_object* v_00_u03b1_860_, lean_object* v_m_861_, lean_object* v_inst_862_, lean_object* v_00_u03b2_863_, lean_object* v_f_864_, lean_object* v_x_865_, size_t v_x_866_, size_t v_x_867_, lean_object* v_x_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_862_, v_f_864_, v_x_865_, v_x_866_, v_x_867_, v_x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___boxed(lean_object* v_00_u03b1_870_, lean_object* v_m_871_, lean_object* v_inst_872_, lean_object* v_00_u03b2_873_, lean_object* v_f_874_, lean_object* v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_x_878_){
_start:
{
size_t v_x_284__boxed_879_; size_t v_x_285__boxed_880_; lean_object* v_res_881_; 
v_x_284__boxed_879_ = lean_unbox_usize(v_x_876_);
lean_dec(v_x_876_);
v_x_285__boxed_880_ = lean_unbox_usize(v_x_877_);
lean_dec(v_x_877_);
v_res_881_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(v_00_u03b1_870_, v_m_871_, v_inst_872_, v_00_u03b2_873_, v_f_874_, v_x_875_, v_x_284__boxed_879_, v_x_285__boxed_880_, v_x_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0(lean_object* v_tail_882_, lean_object* v___x_883_, lean_object* v_toApplicative_884_, lean_object* v_inst_885_, lean_object* v_f_886_, lean_object* v_b_887_){
_start:
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_array_get_size(v_tail_882_);
v___x_889_ = lean_nat_dec_lt(v___x_883_, v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v_toPure_890_; lean_object* v___x_891_; 
lean_dec(v_f_886_);
lean_dec_ref(v_inst_885_);
lean_dec_ref(v_tail_882_);
v_toPure_890_ = lean_ctor_get(v_toApplicative_884_, 1);
lean_inc(v_toPure_890_);
lean_dec_ref(v_toApplicative_884_);
v___x_891_ = lean_apply_2(v_toPure_890_, lean_box(0), v_b_887_);
return v___x_891_;
}
else
{
uint8_t v___x_892_; 
v___x_892_ = lean_nat_dec_le(v___x_888_, v___x_888_);
if (v___x_892_ == 0)
{
if (v___x_889_ == 0)
{
lean_object* v_toPure_893_; lean_object* v___x_894_; 
lean_dec(v_f_886_);
lean_dec_ref(v_inst_885_);
lean_dec_ref(v_tail_882_);
v_toPure_893_ = lean_ctor_get(v_toApplicative_884_, 1);
lean_inc(v_toPure_893_);
lean_dec_ref(v_toApplicative_884_);
v___x_894_ = lean_apply_2(v_toPure_893_, lean_box(0), v_b_887_);
return v___x_894_;
}
else
{
size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; 
lean_dec_ref(v_toApplicative_884_);
v___x_895_ = ((size_t)0ULL);
v___x_896_ = lean_usize_of_nat(v___x_888_);
v___x_897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_885_, v_f_886_, v_tail_882_, v___x_895_, v___x_896_, v_b_887_);
return v___x_897_;
}
}
else
{
size_t v___x_898_; size_t v___x_899_; lean_object* v___x_900_; 
lean_dec_ref(v_toApplicative_884_);
v___x_898_ = ((size_t)0ULL);
v___x_899_ = lean_usize_of_nat(v___x_888_);
v___x_900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_885_, v_f_886_, v_tail_882_, v___x_898_, v___x_899_, v_b_887_);
return v___x_900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed(lean_object* v_tail_901_, lean_object* v___x_902_, lean_object* v_toApplicative_903_, lean_object* v_inst_904_, lean_object* v_f_905_, lean_object* v_b_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_PersistentArray_foldlM___redArg___lam__0(v_tail_901_, v___x_902_, v_toApplicative_903_, v_inst_904_, v_f_905_, v_b_906_);
lean_dec(v___x_902_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object* v_inst_908_, lean_object* v_t_909_, lean_object* v_f_910_, lean_object* v_init_911_, lean_object* v_start_912_){
_start:
{
lean_object* v___x_913_; uint8_t v___x_914_; 
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = lean_nat_dec_eq(v_start_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v_root_915_; lean_object* v_tail_916_; size_t v_shift_917_; lean_object* v_tailOff_918_; uint8_t v___x_919_; 
v_root_915_ = lean_ctor_get(v_t_909_, 0);
lean_inc_ref(v_root_915_);
v_tail_916_ = lean_ctor_get(v_t_909_, 1);
lean_inc_ref(v_tail_916_);
v_shift_917_ = lean_ctor_get_usize(v_t_909_, 4);
v_tailOff_918_ = lean_ctor_get(v_t_909_, 3);
lean_inc(v_tailOff_918_);
lean_dec_ref(v_t_909_);
v___x_919_ = lean_nat_dec_le(v_tailOff_918_, v_start_912_);
if (v___x_919_ == 0)
{
lean_object* v_toApplicative_920_; lean_object* v_toBind_921_; lean_object* v___f_922_; size_t v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
lean_dec(v_tailOff_918_);
v_toApplicative_920_ = lean_ctor_get(v_inst_908_, 0);
v_toBind_921_ = lean_ctor_get(v_inst_908_, 1);
lean_inc(v_toBind_921_);
lean_inc(v_f_910_);
lean_inc_ref(v_inst_908_);
lean_inc_ref(v_toApplicative_920_);
v___f_922_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_922_, 0, v_tail_916_);
lean_closure_set(v___f_922_, 1, v___x_913_);
lean_closure_set(v___f_922_, 2, v_toApplicative_920_);
lean_closure_set(v___f_922_, 3, v_inst_908_);
lean_closure_set(v___f_922_, 4, v_f_910_);
v___x_923_ = lean_usize_of_nat(v_start_912_);
v___x_924_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_908_, v_f_910_, v_root_915_, v___x_923_, v_shift_917_, v_init_911_);
v___x_925_ = lean_apply_4(v_toBind_921_, lean_box(0), lean_box(0), v___x_924_, v___f_922_);
return v___x_925_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
lean_dec_ref(v_root_915_);
v___x_926_ = lean_nat_sub(v_start_912_, v_tailOff_918_);
lean_dec(v_tailOff_918_);
v___x_927_ = lean_array_get_size(v_tail_916_);
v___x_928_ = lean_nat_dec_lt(v___x_926_, v___x_927_);
if (v___x_928_ == 0)
{
lean_object* v_toApplicative_929_; lean_object* v_toPure_930_; lean_object* v___x_931_; 
lean_dec(v___x_926_);
lean_dec_ref(v_tail_916_);
lean_dec(v_f_910_);
v_toApplicative_929_ = lean_ctor_get(v_inst_908_, 0);
lean_inc_ref(v_toApplicative_929_);
lean_dec_ref(v_inst_908_);
v_toPure_930_ = lean_ctor_get(v_toApplicative_929_, 1);
lean_inc(v_toPure_930_);
lean_dec_ref(v_toApplicative_929_);
v___x_931_ = lean_apply_2(v_toPure_930_, lean_box(0), v_init_911_);
return v___x_931_;
}
else
{
uint8_t v___x_932_; 
v___x_932_ = lean_nat_dec_le(v___x_927_, v___x_927_);
if (v___x_932_ == 0)
{
if (v___x_928_ == 0)
{
lean_object* v_toApplicative_933_; lean_object* v_toPure_934_; lean_object* v___x_935_; 
lean_dec(v___x_926_);
lean_dec_ref(v_tail_916_);
lean_dec(v_f_910_);
v_toApplicative_933_ = lean_ctor_get(v_inst_908_, 0);
lean_inc_ref(v_toApplicative_933_);
lean_dec_ref(v_inst_908_);
v_toPure_934_ = lean_ctor_get(v_toApplicative_933_, 1);
lean_inc(v_toPure_934_);
lean_dec_ref(v_toApplicative_933_);
v___x_935_ = lean_apply_2(v_toPure_934_, lean_box(0), v_init_911_);
return v___x_935_;
}
else
{
size_t v___x_936_; size_t v___x_937_; lean_object* v___x_938_; 
v___x_936_ = lean_usize_of_nat(v___x_926_);
lean_dec(v___x_926_);
v___x_937_ = lean_usize_of_nat(v___x_927_);
v___x_938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_908_, v_f_910_, v_tail_916_, v___x_936_, v___x_937_, v_init_911_);
return v___x_938_;
}
}
else
{
size_t v___x_939_; size_t v___x_940_; lean_object* v___x_941_; 
v___x_939_ = lean_usize_of_nat(v___x_926_);
lean_dec(v___x_926_);
v___x_940_ = lean_usize_of_nat(v___x_927_);
v___x_941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_908_, v_f_910_, v_tail_916_, v___x_939_, v___x_940_, v_init_911_);
return v___x_941_;
}
}
}
}
else
{
lean_object* v_toApplicative_942_; lean_object* v_toBind_943_; lean_object* v_root_944_; lean_object* v_tail_945_; lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v_toApplicative_942_ = lean_ctor_get(v_inst_908_, 0);
v_toBind_943_ = lean_ctor_get(v_inst_908_, 1);
lean_inc(v_toBind_943_);
v_root_944_ = lean_ctor_get(v_t_909_, 0);
lean_inc_ref(v_root_944_);
v_tail_945_ = lean_ctor_get(v_t_909_, 1);
lean_inc_ref(v_tail_945_);
lean_dec_ref(v_t_909_);
lean_inc(v_f_910_);
lean_inc_ref(v_inst_908_);
lean_inc_ref(v_toApplicative_942_);
v___f_946_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_946_, 0, v_tail_945_);
lean_closure_set(v___f_946_, 1, v___x_913_);
lean_closure_set(v___f_946_, 2, v_toApplicative_942_);
lean_closure_set(v___f_946_, 3, v_inst_908_);
lean_closure_set(v___f_946_, 4, v_f_910_);
v___x_947_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_908_, v_f_910_, v_root_944_, v_init_911_);
v___x_948_ = lean_apply_4(v_toBind_943_, lean_box(0), lean_box(0), v___x_947_, v___f_946_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___boxed(lean_object* v_inst_949_, lean_object* v_t_950_, lean_object* v_f_951_, lean_object* v_init_952_, lean_object* v_start_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_949_, v_t_950_, v_f_951_, v_init_952_, v_start_953_);
lean_dec(v_start_953_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM(lean_object* v_00_u03b1_955_, lean_object* v_m_956_, lean_object* v_inst_957_, lean_object* v_00_u03b2_958_, lean_object* v_t_959_, lean_object* v_f_960_, lean_object* v_init_961_, lean_object* v_start_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_957_, v_t_959_, v_f_960_, v_init_961_, v_start_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___boxed(lean_object* v_00_u03b1_964_, lean_object* v_m_965_, lean_object* v_inst_966_, lean_object* v_00_u03b2_967_, lean_object* v_t_968_, lean_object* v_f_969_, lean_object* v_init_970_, lean_object* v_start_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_PersistentArray_foldlM(v_00_u03b1_964_, v_m_965_, v_inst_966_, v_00_u03b2_967_, v_t_968_, v_f_969_, v_init_970_, v_start_971_);
lean_dec(v_start_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(lean_object* v_inst_973_, lean_object* v_f_974_, lean_object* v_x_975_, lean_object* v_x_976_){
_start:
{
if (lean_obj_tag(v_x_975_) == 0)
{
lean_object* v_cs_977_; lean_object* v___x_978_; lean_object* v___x_979_; uint8_t v___x_980_; 
v_cs_977_ = lean_ctor_get(v_x_975_, 0);
lean_inc_ref(v_cs_977_);
lean_dec_ref(v_x_975_);
v___x_978_ = lean_array_get_size(v_cs_977_);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_nat_dec_lt(v___x_979_, v___x_978_);
if (v___x_980_ == 0)
{
lean_object* v_toApplicative_981_; lean_object* v_toPure_982_; lean_object* v___x_983_; 
lean_dec_ref(v_cs_977_);
lean_dec(v_f_974_);
v_toApplicative_981_ = lean_ctor_get(v_inst_973_, 0);
lean_inc_ref(v_toApplicative_981_);
lean_dec_ref(v_inst_973_);
v_toPure_982_ = lean_ctor_get(v_toApplicative_981_, 1);
lean_inc(v_toPure_982_);
lean_dec_ref(v_toApplicative_981_);
v___x_983_ = lean_apply_2(v_toPure_982_, lean_box(0), v_x_976_);
return v___x_983_;
}
else
{
lean_object* v___f_984_; size_t v___x_985_; size_t v___x_986_; lean_object* v___x_987_; 
lean_inc_ref(v_inst_973_);
v___f_984_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_984_, 0, v_inst_973_);
lean_closure_set(v___f_984_, 1, v_f_974_);
v___x_985_ = lean_usize_of_nat(v___x_978_);
v___x_986_ = ((size_t)0ULL);
v___x_987_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_973_, v___f_984_, v_cs_977_, v___x_985_, v___x_986_, v_x_976_);
return v___x_987_;
}
}
else
{
lean_object* v_vs_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_vs_988_ = lean_ctor_get(v_x_975_, 0);
lean_inc_ref(v_vs_988_);
lean_dec_ref(v_x_975_);
v___x_989_ = lean_array_get_size(v_vs_988_);
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = lean_nat_dec_lt(v___x_990_, v___x_989_);
if (v___x_991_ == 0)
{
lean_object* v_toApplicative_992_; lean_object* v_toPure_993_; lean_object* v___x_994_; 
lean_dec_ref(v_vs_988_);
lean_dec(v_f_974_);
v_toApplicative_992_ = lean_ctor_get(v_inst_973_, 0);
lean_inc_ref(v_toApplicative_992_);
lean_dec_ref(v_inst_973_);
v_toPure_993_ = lean_ctor_get(v_toApplicative_992_, 1);
lean_inc(v_toPure_993_);
lean_dec_ref(v_toApplicative_992_);
v___x_994_ = lean_apply_2(v_toPure_993_, lean_box(0), v_x_976_);
return v___x_994_;
}
else
{
size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_usize_of_nat(v___x_989_);
v___x_996_ = ((size_t)0ULL);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_973_, v_f_974_, v_vs_988_, v___x_995_, v___x_996_, v_x_976_);
return v___x_997_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0(lean_object* v_inst_998_, lean_object* v_f_999_, lean_object* v_c_1000_, lean_object* v_b_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_998_, v_f_999_, v_c_1000_, v_b_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux(lean_object* v_00_u03b1_1003_, lean_object* v_m_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_inst_1006_, lean_object* v_f_1007_, lean_object* v_x_1008_, lean_object* v_x_1009_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1006_, v_f_1007_, v_x_1008_, v_x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg___lam__0(lean_object* v_inst_1011_, lean_object* v_f_1012_, lean_object* v_root_1013_, lean_object* v_____do__lift_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_1011_, v_f_1012_, v_root_1013_, v_____do__lift_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object* v_inst_1016_, lean_object* v_t_1017_, lean_object* v_f_1018_, lean_object* v_init_1019_){
_start:
{
lean_object* v_toApplicative_1020_; lean_object* v_toBind_1021_; lean_object* v_root_1022_; lean_object* v_tail_1023_; lean_object* v___f_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v_toApplicative_1020_ = lean_ctor_get(v_inst_1016_, 0);
v_toBind_1021_ = lean_ctor_get(v_inst_1016_, 1);
lean_inc(v_toBind_1021_);
v_root_1022_ = lean_ctor_get(v_t_1017_, 0);
lean_inc_ref(v_root_1022_);
v_tail_1023_ = lean_ctor_get(v_t_1017_, 1);
lean_inc_ref(v_tail_1023_);
lean_dec_ref(v_t_1017_);
lean_inc(v_f_1018_);
lean_inc_ref(v_inst_1016_);
v___f_1024_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1024_, 0, v_inst_1016_);
lean_closure_set(v___f_1024_, 1, v_f_1018_);
lean_closure_set(v___f_1024_, 2, v_root_1022_);
v___x_1025_ = lean_array_get_size(v_tail_1023_);
v___x_1026_ = lean_unsigned_to_nat(0u);
v___x_1027_ = lean_nat_dec_lt(v___x_1026_, v___x_1025_);
if (v___x_1027_ == 0)
{
lean_object* v_toPure_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
lean_inc_ref(v_toApplicative_1020_);
lean_dec_ref(v_tail_1023_);
lean_dec(v_f_1018_);
lean_dec_ref(v_inst_1016_);
v_toPure_1028_ = lean_ctor_get(v_toApplicative_1020_, 1);
lean_inc(v_toPure_1028_);
lean_dec_ref(v_toApplicative_1020_);
v___x_1029_ = lean_apply_2(v_toPure_1028_, lean_box(0), v_init_1019_);
v___x_1030_ = lean_apply_4(v_toBind_1021_, lean_box(0), lean_box(0), v___x_1029_, v___f_1024_);
return v___x_1030_;
}
else
{
size_t v___x_1031_; size_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1031_ = lean_usize_of_nat(v___x_1025_);
v___x_1032_ = ((size_t)0ULL);
v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1016_, v_f_1018_, v_tail_1023_, v___x_1031_, v___x_1032_, v_init_1019_);
v___x_1034_ = lean_apply_4(v_toBind_1021_, lean_box(0), lean_box(0), v___x_1033_, v___f_1024_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM(lean_object* v_00_u03b1_1035_, lean_object* v_m_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_inst_1038_, lean_object* v_t_1039_, lean_object* v_f_1040_, lean_object* v_init_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_1038_, v_t_1039_, v_f_1040_, v_init_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__0(lean_object* v_toPure_1043_, lean_object* v_____s_1044_){
_start:
{
lean_object* v_fst_1045_; 
v_fst_1045_ = lean_ctor_get(v_____s_1044_, 0);
if (lean_obj_tag(v_fst_1045_) == 0)
{
lean_object* v_snd_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_snd_1046_ = lean_ctor_get(v_____s_1044_, 1);
lean_inc(v_snd_1046_);
lean_dec_ref(v_____s_1044_);
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v_snd_1046_);
v___x_1048_ = lean_apply_2(v_toPure_1043_, lean_box(0), v___x_1047_);
return v___x_1048_;
}
else
{
lean_object* v_val_1049_; lean_object* v___x_1050_; 
lean_inc_ref(v_fst_1045_);
lean_dec_ref(v_____s_1044_);
v_val_1049_ = lean_ctor_get(v_fst_1045_, 0);
lean_inc(v_val_1049_);
lean_dec_ref(v_fst_1045_);
v___x_1050_ = lean_apply_2(v_toPure_1043_, lean_box(0), v_val_1049_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__1(lean_object* v_snd_1051_, lean_object* v_toPure_1052_, lean_object* v___x_1053_, lean_object* v_____do__lift_1054_){
_start:
{
if (lean_obj_tag(v_____do__lift_1054_) == 0)
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec(v___x_1053_);
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_____do__lift_1054_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v_snd_1051_);
v___x_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
v___x_1058_ = lean_apply_2(v_toPure_1052_, lean_box(0), v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_snd_1051_);
v_a_1059_ = lean_ctor_get(v_____do__lift_1054_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_____do__lift_1054_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1061_ = v_____do__lift_1054_;
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v_____do__lift_1054_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1068_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1053_);
lean_ctor_set(v___x_1063_, 1, v_a_1059_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 0, v___x_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_apply_2(v_toPure_1052_, lean_box(0), v___x_1065_);
return v___x_1066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__5(lean_object* v_toPure_1069_, lean_object* v___x_1070_, lean_object* v_f_1071_, lean_object* v_toBind_1072_, lean_object* v_a_1073_, lean_object* v_x_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_snd_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_snd_1076_ = lean_ctor_get(v___y_1075_, 1);
lean_inc_n(v_snd_1076_, 2);
lean_dec_ref(v___y_1075_);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1077_, 0, v_snd_1076_);
lean_closure_set(v___f_1077_, 1, v_toPure_1069_);
lean_closure_set(v___f_1077_, 2, v___x_1070_);
v___x_1078_ = lean_apply_2(v_f_1071_, v_a_1073_, v_snd_1076_);
v___x_1079_ = lean_apply_4(v_toBind_1072_, lean_box(0), lean_box(0), v___x_1078_, v___f_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg(lean_object* v_inst_1080_, lean_object* v_f_1081_, lean_object* v_n_1082_, lean_object* v_b_1083_){
_start:
{
if (lean_obj_tag(v_n_1082_) == 0)
{
lean_object* v_toApplicative_1084_; lean_object* v_toBind_1085_; lean_object* v_toPure_1086_; lean_object* v_cs_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___f_1090_; lean_object* v___x_1091_; size_t v_sz_1092_; size_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_toApplicative_1084_ = lean_ctor_get(v_inst_1080_, 0);
v_toBind_1085_ = lean_ctor_get(v_inst_1080_, 1);
lean_inc_n(v_toBind_1085_, 2);
v_toPure_1086_ = lean_ctor_get(v_toApplicative_1084_, 1);
v_cs_1087_ = lean_ctor_get(v_n_1082_, 0);
lean_inc_ref(v_cs_1087_);
lean_dec_ref(v_n_1082_);
lean_inc_n(v_toPure_1086_, 2);
v___f_1088_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1088_, 0, v_toPure_1086_);
v___x_1089_ = lean_box(0);
lean_inc_ref(v_inst_1080_);
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__2), 8, 5);
lean_closure_set(v___f_1090_, 0, v_toPure_1086_);
lean_closure_set(v___f_1090_, 1, v___x_1089_);
lean_closure_set(v___f_1090_, 2, v_inst_1080_);
lean_closure_set(v___f_1090_, 3, v_f_1081_);
lean_closure_set(v___f_1090_, 4, v_toBind_1085_);
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v_b_1083_);
v_sz_1092_ = lean_array_size(v_cs_1087_);
v___x_1093_ = ((size_t)0ULL);
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1080_, v_cs_1087_, v___f_1090_, v_sz_1092_, v___x_1093_, v___x_1091_);
v___x_1095_ = lean_apply_4(v_toBind_1085_, lean_box(0), lean_box(0), v___x_1094_, v___f_1088_);
return v___x_1095_;
}
else
{
lean_object* v_toApplicative_1096_; lean_object* v_toBind_1097_; lean_object* v_toPure_1098_; lean_object* v_vs_1099_; lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; size_t v_sz_1104_; size_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v_toApplicative_1096_ = lean_ctor_get(v_inst_1080_, 0);
v_toBind_1097_ = lean_ctor_get(v_inst_1080_, 1);
lean_inc_n(v_toBind_1097_, 2);
v_toPure_1098_ = lean_ctor_get(v_toApplicative_1096_, 1);
v_vs_1099_ = lean_ctor_get(v_n_1082_, 0);
lean_inc_ref(v_vs_1099_);
lean_dec_ref(v_n_1082_);
lean_inc_n(v_toPure_1098_, 2);
v___f_1100_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1100_, 0, v_toPure_1098_);
v___x_1101_ = lean_box(0);
v___f_1102_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__5), 7, 4);
lean_closure_set(v___f_1102_, 0, v_toPure_1098_);
lean_closure_set(v___f_1102_, 1, v___x_1101_);
lean_closure_set(v___f_1102_, 2, v_f_1081_);
lean_closure_set(v___f_1102_, 3, v_toBind_1097_);
v___x_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v_b_1083_);
v_sz_1104_ = lean_array_size(v_vs_1099_);
v___x_1105_ = ((size_t)0ULL);
v___x_1106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1080_, v_vs_1099_, v___f_1102_, v_sz_1104_, v___x_1105_, v___x_1103_);
v___x_1107_ = lean_apply_4(v_toBind_1097_, lean_box(0), lean_box(0), v___x_1106_, v___f_1100_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2(lean_object* v_toPure_1108_, lean_object* v___x_1109_, lean_object* v_inst_1110_, lean_object* v_f_1111_, lean_object* v_toBind_1112_, lean_object* v_a_1113_, lean_object* v_x_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_snd_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v_snd_1116_ = lean_ctor_get(v___y_1115_, 1);
lean_inc_n(v_snd_1116_, 2);
lean_dec_ref(v___y_1115_);
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1117_, 0, v_snd_1116_);
lean_closure_set(v___f_1117_, 1, v_toPure_1108_);
lean_closure_set(v___f_1117_, 2, v___x_1109_);
v___x_1118_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1110_, v_f_1111_, v_a_1113_, v_snd_1116_);
v___x_1119_ = lean_apply_4(v_toBind_1112_, lean_box(0), lean_box(0), v___x_1118_, v___f_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux(lean_object* v_00_u03b1_1120_, lean_object* v_00_u03b2_1121_, lean_object* v_m_1122_, lean_object* v_inst_1123_, lean_object* v_inh_1124_, lean_object* v_f_1125_, lean_object* v_n_1126_, lean_object* v_b_1127_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1123_, v_f_1125_, v_n_1126_, v_b_1127_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_m_1131_, lean_object* v_inst_1132_, lean_object* v_inh_1133_, lean_object* v_f_1134_, lean_object* v_n_1135_, lean_object* v_b_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_PersistentArray_forInAux(v_00_u03b1_1129_, v_00_u03b2_1130_, v_m_1131_, v_inst_1132_, v_inh_1133_, v_f_1134_, v_n_1135_, v_b_1136_);
lean_dec(v_inh_1133_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__0(lean_object* v_toPure_1138_, lean_object* v_____s_1139_){
_start:
{
lean_object* v_fst_1140_; 
v_fst_1140_ = lean_ctor_get(v_____s_1139_, 0);
if (lean_obj_tag(v_fst_1140_) == 0)
{
lean_object* v_snd_1141_; lean_object* v___x_1142_; 
v_snd_1141_ = lean_ctor_get(v_____s_1139_, 1);
lean_inc(v_snd_1141_);
lean_dec_ref(v_____s_1139_);
v___x_1142_ = lean_apply_2(v_toPure_1138_, lean_box(0), v_snd_1141_);
return v___x_1142_;
}
else
{
lean_object* v_val_1143_; lean_object* v___x_1144_; 
lean_inc_ref(v_fst_1140_);
lean_dec_ref(v_____s_1139_);
v_val_1143_ = lean_ctor_get(v_fst_1140_, 0);
lean_inc(v_val_1143_);
lean_dec_ref(v_fst_1140_);
v___x_1144_ = lean_apply_2(v_toPure_1138_, lean_box(0), v_val_1143_);
return v___x_1144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__1(lean_object* v_snd_1145_, lean_object* v_toPure_1146_, lean_object* v___x_1147_, lean_object* v_____do__lift_1148_){
_start:
{
if (lean_obj_tag(v_____do__lift_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v___x_1147_);
v_a_1149_ = lean_ctor_get(v_____do__lift_1148_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_____do__lift_1148_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1151_ = v_____do__lift_1148_;
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v_____do__lift_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1159_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1153_, 0, v_a_1149_);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v_snd_1145_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1154_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_apply_2(v_toPure_1146_, lean_box(0), v___x_1156_);
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_snd_1145_);
v_a_1160_ = lean_ctor_get(v_____do__lift_1148_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_____do__lift_1148_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1162_ = v_____do__lift_1148_;
v_isShared_1163_ = v_isSharedCheck_1169_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v_____do__lift_1148_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1169_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
v___x_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1147_);
lean_ctor_set(v___x_1164_, 1, v_a_1160_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 0, v___x_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_apply_2(v_toPure_1146_, lean_box(0), v___x_1166_);
return v___x_1167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__2(lean_object* v_toPure_1170_, lean_object* v___x_1171_, lean_object* v_f_1172_, lean_object* v_toBind_1173_, lean_object* v_a_1174_, lean_object* v_x_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v_snd_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_snd_1177_ = lean_ctor_get(v___y_1176_, 1);
lean_inc_n(v_snd_1177_, 2);
lean_dec_ref(v___y_1176_);
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1178_, 0, v_snd_1177_);
lean_closure_set(v___f_1178_, 1, v_toPure_1170_);
lean_closure_set(v___f_1178_, 2, v___x_1171_);
v___x_1179_ = lean_apply_2(v_f_1172_, v_a_1174_, v_snd_1177_);
v___x_1180_ = lean_apply_4(v_toBind_1173_, lean_box(0), lean_box(0), v___x_1179_, v___f_1178_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___lam__3(lean_object* v_toPure_1181_, lean_object* v_f_1182_, lean_object* v_toBind_1183_, lean_object* v_tail_1184_, lean_object* v_inst_1185_, lean_object* v___f_1186_, lean_object* v_____do__lift_1187_){
_start:
{
if (lean_obj_tag(v_____do__lift_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; 
lean_dec(v___f_1186_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_tail_1184_);
lean_dec(v_toBind_1183_);
lean_dec(v_f_1182_);
v_a_1188_ = lean_ctor_get(v_____do__lift_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref(v_____do__lift_1187_);
v___x_1189_ = lean_apply_2(v_toPure_1181_, lean_box(0), v_a_1188_);
return v___x_1189_;
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; size_t v_sz_1194_; size_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_a_1190_ = lean_ctor_get(v_____do__lift_1187_, 0);
lean_inc(v_a_1190_);
lean_dec_ref(v_____do__lift_1187_);
v___x_1191_ = lean_box(0);
lean_inc(v_toBind_1183_);
v___f_1192_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__2), 7, 4);
lean_closure_set(v___f_1192_, 0, v_toPure_1181_);
lean_closure_set(v___f_1192_, 1, v___x_1191_);
lean_closure_set(v___f_1192_, 2, v_f_1182_);
lean_closure_set(v___f_1192_, 3, v_toBind_1183_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v_a_1190_);
v_sz_1194_ = lean_array_size(v_tail_1184_);
v___x_1195_ = ((size_t)0ULL);
v___x_1196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1185_, v_tail_1184_, v___f_1192_, v_sz_1194_, v___x_1195_, v___x_1193_);
v___x_1197_ = lean_apply_4(v_toBind_1183_, lean_box(0), lean_box(0), v___x_1196_, v___f_1186_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg(lean_object* v_inst_1198_, lean_object* v_t_1199_, lean_object* v_init_1200_, lean_object* v_f_1201_){
_start:
{
lean_object* v_toApplicative_1202_; lean_object* v_toBind_1203_; lean_object* v_root_1204_; lean_object* v_tail_1205_; lean_object* v_toPure_1206_; lean_object* v___x_1207_; lean_object* v___f_1208_; lean_object* v___f_1209_; lean_object* v___x_1210_; 
v_toApplicative_1202_ = lean_ctor_get(v_inst_1198_, 0);
v_toBind_1203_ = lean_ctor_get(v_inst_1198_, 1);
lean_inc_n(v_toBind_1203_, 2);
v_root_1204_ = lean_ctor_get(v_t_1199_, 0);
lean_inc_ref(v_root_1204_);
v_tail_1205_ = lean_ctor_get(v_t_1199_, 1);
lean_inc_ref(v_tail_1205_);
lean_dec_ref(v_t_1199_);
v_toPure_1206_ = lean_ctor_get(v_toApplicative_1202_, 1);
lean_inc_n(v_toPure_1206_, 2);
lean_inc(v_f_1201_);
lean_inc_ref(v_inst_1198_);
v___x_1207_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1198_, v_f_1201_, v_root_1204_, v_init_1200_);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1208_, 0, v_toPure_1206_);
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1209_, 0, v_toPure_1206_);
lean_closure_set(v___f_1209_, 1, v_f_1201_);
lean_closure_set(v___f_1209_, 2, v_toBind_1203_);
lean_closure_set(v___f_1209_, 3, v_tail_1205_);
lean_closure_set(v___f_1209_, 4, v_inst_1198_);
lean_closure_set(v___f_1209_, 5, v___f_1208_);
v___x_1210_ = lean_apply_4(v_toBind_1203_, lean_box(0), lean_box(0), v___x_1207_, v___f_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn(lean_object* v_00_u03b1_1211_, lean_object* v_m_1212_, lean_object* v_inst_1213_, lean_object* v_00_u03b2_1214_, lean_object* v_t_1215_, lean_object* v_init_1216_, lean_object* v_f_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1213_, v_t_1215_, v_init_1216_, v_f_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad___redArg(lean_object* v_inst_1219_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn), 7, 3);
lean_closure_set(v___x_1220_, 0, lean_box(0));
lean_closure_set(v___x_1220_, 1, lean_box(0));
lean_closure_set(v___x_1220_, 2, v_inst_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad(lean_object* v_00_u03b1_1221_, lean_object* v_m_1222_, lean_object* v_inst_1223_){
_start:
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn), 7, 3);
lean_closure_set(v___x_1224_, 0, lean_box(0));
lean_closure_set(v___x_1224_, 1, lean_box(0));
lean_closure_set(v___x_1224_, 2, v_inst_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(lean_object* v_toPure_1225_, lean_object* v_____s_1226_){
_start:
{
lean_object* v_fst_1227_; 
v_fst_1227_ = lean_ctor_get(v_____s_1226_, 0);
lean_inc(v_fst_1227_);
lean_dec_ref(v_____s_1226_);
if (lean_obj_tag(v_fst_1227_) == 0)
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_box(0);
v___x_1229_ = lean_apply_2(v_toPure_1225_, lean_box(0), v___x_1228_);
return v___x_1229_;
}
else
{
lean_object* v_val_1230_; lean_object* v___x_1231_; 
v_val_1230_ = lean_ctor_get(v_fst_1227_, 0);
lean_inc(v_val_1230_);
lean_dec_ref(v_fst_1227_);
v___x_1231_ = lean_apply_2(v_toPure_1225_, lean_box(0), v_val_1230_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(lean_object* v___x_1232_, lean_object* v_toPure_1233_, lean_object* v___x_1234_, lean_object* v_____do__lift_1235_){
_start:
{
if (lean_obj_tag(v_____do__lift_1235_) == 1)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec_ref(v___x_1234_);
v___x_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1236_, 0, v_____do__lift_1235_);
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v___x_1232_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
v___x_1239_ = lean_apply_2(v_toPure_1233_, lean_box(0), v___x_1238_);
return v___x_1239_;
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec(v_____do__lift_1235_);
v___x_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1234_);
v___x_1241_ = lean_apply_2(v_toPure_1233_, lean_box(0), v___x_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(lean_object* v_f_1242_, lean_object* v_toBind_1243_, lean_object* v___f_1244_, lean_object* v_a_1245_, lean_object* v_x_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = lean_apply_1(v_f_1242_, v_a_1245_);
v___x_1249_ = lean_apply_4(v_toBind_1243_, lean_box(0), lean_box(0), v___x_1248_, v___f_1244_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(lean_object* v_f_1250_, lean_object* v_toBind_1251_, lean_object* v___f_1252_, lean_object* v_a_1253_, lean_object* v_x_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(v_f_1250_, v_toBind_1251_, v___f_1252_, v_a_1253_, v_x_1254_, v___y_1255_);
lean_dec_ref(v___y_1255_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(lean_object* v_inst_1260_, lean_object* v_f_1261_, lean_object* v_toBind_1262_, lean_object* v___f_1263_, lean_object* v_a_1264_, lean_object* v_x_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(v_inst_1260_, v_f_1261_, v_toBind_1262_, v___f_1263_, v_a_1264_, v_x_1265_, v___y_1266_);
lean_dec_ref(v___y_1266_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg(lean_object* v_inst_1268_, lean_object* v_f_1269_, lean_object* v_x_1270_){
_start:
{
if (lean_obj_tag(v_x_1270_) == 0)
{
lean_object* v_toApplicative_1271_; lean_object* v_cs_1272_; lean_object* v_toBind_1273_; lean_object* v_toPure_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___f_1277_; lean_object* v___f_1278_; lean_object* v___f_1279_; size_t v_sz_1280_; size_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
v_toApplicative_1271_ = lean_ctor_get(v_inst_1268_, 0);
v_cs_1272_ = lean_ctor_get(v_x_1270_, 0);
lean_inc_ref(v_cs_1272_);
lean_dec_ref(v_x_1270_);
v_toBind_1273_ = lean_ctor_get(v_inst_1268_, 1);
lean_inc_n(v_toBind_1273_, 2);
v_toPure_1274_ = lean_ctor_get(v_toApplicative_1271_, 1);
v___x_1275_ = lean_box(0);
v___x_1276_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1274_, 2);
v___f_1277_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1277_, 0, v_toPure_1274_);
v___f_1278_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1278_, 0, v___x_1275_);
lean_closure_set(v___f_1278_, 1, v_toPure_1274_);
lean_closure_set(v___f_1278_, 2, v___x_1276_);
lean_inc_ref(v_inst_1268_);
v___f_1279_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1279_, 0, v_inst_1268_);
lean_closure_set(v___f_1279_, 1, v_f_1269_);
lean_closure_set(v___f_1279_, 2, v_toBind_1273_);
lean_closure_set(v___f_1279_, 3, v___f_1278_);
v_sz_1280_ = lean_array_size(v_cs_1272_);
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1268_, v_cs_1272_, v___f_1279_, v_sz_1280_, v___x_1281_, v___x_1276_);
v___x_1283_ = lean_apply_4(v_toBind_1273_, lean_box(0), lean_box(0), v___x_1282_, v___f_1277_);
return v___x_1283_;
}
else
{
lean_object* v_toApplicative_1284_; lean_object* v_vs_1285_; lean_object* v_toBind_1286_; lean_object* v_toPure_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___f_1290_; lean_object* v___f_1291_; lean_object* v___f_1292_; size_t v_sz_1293_; size_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_toApplicative_1284_ = lean_ctor_get(v_inst_1268_, 0);
v_vs_1285_ = lean_ctor_get(v_x_1270_, 0);
lean_inc_ref(v_vs_1285_);
lean_dec_ref(v_x_1270_);
v_toBind_1286_ = lean_ctor_get(v_inst_1268_, 1);
lean_inc_n(v_toBind_1286_, 2);
v_toPure_1287_ = lean_ctor_get(v_toApplicative_1284_, 1);
v___x_1288_ = lean_box(0);
v___x_1289_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1287_, 2);
v___f_1290_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1290_, 0, v_toPure_1287_);
v___f_1291_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1291_, 0, v___x_1288_);
lean_closure_set(v___f_1291_, 1, v_toPure_1287_);
lean_closure_set(v___f_1291_, 2, v___x_1289_);
v___f_1292_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1292_, 0, v_f_1269_);
lean_closure_set(v___f_1292_, 1, v_toBind_1286_);
lean_closure_set(v___f_1292_, 2, v___f_1291_);
v_sz_1293_ = lean_array_size(v_vs_1285_);
v___x_1294_ = ((size_t)0ULL);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1268_, v_vs_1285_, v___f_1292_, v_sz_1293_, v___x_1294_, v___x_1289_);
v___x_1296_ = lean_apply_4(v_toBind_1286_, lean_box(0), lean_box(0), v___x_1295_, v___f_1290_);
return v___x_1296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(lean_object* v_inst_1297_, lean_object* v_f_1298_, lean_object* v_toBind_1299_, lean_object* v___f_1300_, lean_object* v_a_1301_, lean_object* v_x_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1297_, v_f_1298_, v_a_1301_);
v___x_1305_ = lean_apply_4(v_toBind_1299_, lean_box(0), lean_box(0), v___x_1304_, v___f_1300_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux(lean_object* v_00_u03b1_1306_, lean_object* v_m_1307_, lean_object* v_inst_1308_, lean_object* v_00_u03b2_1309_, lean_object* v_f_1310_, lean_object* v_x_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1308_, v_f_1310_, v_x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(lean_object* v_toPure_1313_, lean_object* v_____do__lift_1314_, lean_object* v_____s_1315_){
_start:
{
lean_object* v_fst_1316_; 
v_fst_1316_ = lean_ctor_get(v_____s_1315_, 0);
lean_inc(v_fst_1316_);
lean_dec_ref(v_____s_1315_);
if (lean_obj_tag(v_fst_1316_) == 0)
{
lean_object* v___x_1317_; 
v___x_1317_ = lean_apply_2(v_toPure_1313_, lean_box(0), v_____do__lift_1314_);
return v___x_1317_;
}
else
{
lean_object* v_val_1318_; lean_object* v___x_1319_; 
lean_dec(v_____do__lift_1314_);
v_val_1318_ = lean_ctor_get(v_fst_1316_, 0);
lean_inc(v_val_1318_);
lean_dec_ref(v_fst_1316_);
v___x_1319_ = lean_apply_2(v_toPure_1313_, lean_box(0), v_val_1318_);
return v___x_1319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(lean_object* v___x_1320_, lean_object* v_toPure_1321_, lean_object* v___x_1322_, lean_object* v_____do__lift_1323_){
_start:
{
if (lean_obj_tag(v_____do__lift_1323_) == 1)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec_ref(v___x_1322_);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_____do__lift_1323_);
v___x_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v___x_1320_);
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
v___x_1327_ = lean_apply_2(v_toPure_1321_, lean_box(0), v___x_1326_);
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec(v_____do__lift_1323_);
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1322_);
v___x_1329_ = lean_apply_2(v_toPure_1321_, lean_box(0), v___x_1328_);
return v___x_1329_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1330_, lean_object* v_toBind_1331_, lean_object* v___f_1332_, lean_object* v_a_1333_, lean_object* v_x_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_apply_1(v_f_1330_, v_a_1333_);
v___x_1337_ = lean_apply_4(v_toBind_1331_, lean_box(0), lean_box(0), v___x_1336_, v___f_1332_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1338_, lean_object* v_toBind_1339_, lean_object* v___f_1340_, lean_object* v_a_1341_, lean_object* v_x_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(v_f_1338_, v_toBind_1339_, v___f_1340_, v_a_1341_, v_x_1342_, v___y_1343_);
lean_dec_ref(v___y_1343_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(lean_object* v_toPure_1345_, lean_object* v_f_1346_, lean_object* v_toBind_1347_, lean_object* v_tail_1348_, lean_object* v_inst_1349_, lean_object* v_____do__lift_1350_){
_start:
{
if (lean_obj_tag(v_____do__lift_1350_) == 0)
{
lean_object* v___f_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___f_1354_; lean_object* v___f_1355_; size_t v_sz_1356_; size_t v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_inc(v_toPure_1345_);
v___f_1351_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1351_, 0, v_toPure_1345_);
lean_closure_set(v___f_1351_, 1, v_____do__lift_1350_);
v___x_1352_ = lean_box(0);
v___x_1353_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1354_, 0, v___x_1352_);
lean_closure_set(v___f_1354_, 1, v_toPure_1345_);
lean_closure_set(v___f_1354_, 2, v___x_1353_);
lean_inc(v_toBind_1347_);
v___f_1355_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1355_, 0, v_f_1346_);
lean_closure_set(v___f_1355_, 1, v_toBind_1347_);
lean_closure_set(v___f_1355_, 2, v___f_1354_);
v_sz_1356_ = lean_array_size(v_tail_1348_);
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1349_, v_tail_1348_, v___f_1355_, v_sz_1356_, v___x_1357_, v___x_1353_);
v___x_1359_ = lean_apply_4(v_toBind_1347_, lean_box(0), lean_box(0), v___x_1358_, v___f_1351_);
return v___x_1359_;
}
else
{
lean_object* v___x_1360_; 
lean_dec_ref(v_inst_1349_);
lean_dec_ref(v_tail_1348_);
lean_dec(v_toBind_1347_);
lean_dec(v_f_1346_);
v___x_1360_ = lean_apply_2(v_toPure_1345_, lean_box(0), v_____do__lift_1350_);
return v___x_1360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object* v_inst_1361_, lean_object* v_t_1362_, lean_object* v_f_1363_){
_start:
{
lean_object* v_toApplicative_1364_; lean_object* v_toBind_1365_; lean_object* v_root_1366_; lean_object* v_tail_1367_; lean_object* v_toPure_1368_; lean_object* v___x_1369_; lean_object* v___f_1370_; lean_object* v___x_1371_; 
v_toApplicative_1364_ = lean_ctor_get(v_inst_1361_, 0);
v_toBind_1365_ = lean_ctor_get(v_inst_1361_, 1);
lean_inc_n(v_toBind_1365_, 2);
v_root_1366_ = lean_ctor_get(v_t_1362_, 0);
lean_inc_ref(v_root_1366_);
v_tail_1367_ = lean_ctor_get(v_t_1362_, 1);
lean_inc_ref(v_tail_1367_);
lean_dec_ref(v_t_1362_);
v_toPure_1368_ = lean_ctor_get(v_toApplicative_1364_, 1);
lean_inc(v_toPure_1368_);
lean_inc(v_f_1363_);
lean_inc_ref(v_inst_1361_);
v___x_1369_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1361_, v_f_1363_, v_root_1366_);
v___f_1370_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1370_, 0, v_toPure_1368_);
lean_closure_set(v___f_1370_, 1, v_f_1363_);
lean_closure_set(v___f_1370_, 2, v_toBind_1365_);
lean_closure_set(v___f_1370_, 3, v_tail_1367_);
lean_closure_set(v___f_1370_, 4, v_inst_1361_);
v___x_1371_ = lean_apply_4(v_toBind_1365_, lean_box(0), lean_box(0), v___x_1369_, v___f_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f(lean_object* v_00_u03b1_1372_, lean_object* v_m_1373_, lean_object* v_inst_1374_, lean_object* v_00_u03b2_1375_, lean_object* v_t_1376_, lean_object* v_f_1377_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_1374_, v_t_1376_, v_f_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg(lean_object* v_inst_1379_, lean_object* v_f_1380_, lean_object* v_x_1381_){
_start:
{
if (lean_obj_tag(v_x_1381_) == 0)
{
lean_object* v_cs_1382_; lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_cs_1382_ = lean_ctor_get(v_x_1381_, 0);
lean_inc_ref(v_cs_1382_);
lean_dec_ref(v_x_1381_);
lean_inc_ref(v_inst_1379_);
v___f_1383_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1383_, 0, v_inst_1379_);
lean_closure_set(v___f_1383_, 1, v_f_1380_);
v___x_1384_ = lean_array_get_size(v_cs_1382_);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1379_, v___f_1383_, v_cs_1382_, v___x_1384_, lean_box(0));
return v___x_1385_;
}
else
{
lean_object* v_vs_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v_vs_1386_ = lean_ctor_get(v_x_1381_, 0);
lean_inc_ref(v_vs_1386_);
lean_dec_ref(v_x_1381_);
v___x_1387_ = lean_array_get_size(v_vs_1386_);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1379_, v_f_1380_, v_vs_1386_, v___x_1387_, lean_box(0));
return v___x_1388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(lean_object* v_inst_1389_, lean_object* v_f_1390_, lean_object* v_c_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1389_, v_f_1390_, v_c_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux(lean_object* v_00_u03b1_1393_, lean_object* v_m_1394_, lean_object* v_inst_1395_, lean_object* v_00_u03b2_1396_, lean_object* v_f_1397_, lean_object* v_x_1398_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1395_, v_f_1397_, v_x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(lean_object* v_inst_1400_, lean_object* v_f_1401_, lean_object* v_root_1402_, lean_object* v_toPure_1403_, lean_object* v_____do__lift_1404_){
_start:
{
if (lean_obj_tag(v_____do__lift_1404_) == 0)
{
lean_object* v___x_1405_; 
lean_dec(v_toPure_1403_);
v___x_1405_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1400_, v_f_1401_, v_root_1402_);
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; 
lean_dec_ref(v_root_1402_);
lean_dec(v_f_1401_);
lean_dec_ref(v_inst_1400_);
v___x_1406_ = lean_apply_2(v_toPure_1403_, lean_box(0), v_____do__lift_1404_);
return v___x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object* v_inst_1407_, lean_object* v_t_1408_, lean_object* v_f_1409_){
_start:
{
lean_object* v_toApplicative_1410_; lean_object* v_toBind_1411_; lean_object* v_root_1412_; lean_object* v_tail_1413_; lean_object* v_toPure_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___f_1417_; lean_object* v___x_1418_; 
v_toApplicative_1410_ = lean_ctor_get(v_inst_1407_, 0);
v_toBind_1411_ = lean_ctor_get(v_inst_1407_, 1);
lean_inc(v_toBind_1411_);
v_root_1412_ = lean_ctor_get(v_t_1408_, 0);
lean_inc_ref(v_root_1412_);
v_tail_1413_ = lean_ctor_get(v_t_1408_, 1);
lean_inc_ref(v_tail_1413_);
lean_dec_ref(v_t_1408_);
v_toPure_1414_ = lean_ctor_get(v_toApplicative_1410_, 1);
lean_inc(v_toPure_1414_);
v___x_1415_ = lean_array_get_size(v_tail_1413_);
lean_inc(v_f_1409_);
lean_inc_ref(v_inst_1407_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1407_, v_f_1409_, v_tail_1413_, v___x_1415_, lean_box(0));
v___f_1417_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1417_, 0, v_inst_1407_);
lean_closure_set(v___f_1417_, 1, v_f_1409_);
lean_closure_set(v___f_1417_, 2, v_root_1412_);
lean_closure_set(v___f_1417_, 3, v_toPure_1414_);
v___x_1418_ = lean_apply_4(v_toBind_1411_, lean_box(0), lean_box(0), v___x_1416_, v___f_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f(lean_object* v_00_u03b1_1419_, lean_object* v_m_1420_, lean_object* v_inst_1421_, lean_object* v_00_u03b2_1422_, lean_object* v_t_1423_, lean_object* v_f_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_1421_, v_t_1423_, v_f_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__1(lean_object* v_f_1426_, lean_object* v_x_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_apply_1(v_f_1426_, v___y_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg(lean_object* v_inst_1430_, lean_object* v_f_1431_, lean_object* v_x_1432_){
_start:
{
if (lean_obj_tag(v_x_1432_) == 0)
{
lean_object* v_cs_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_cs_1433_ = lean_ctor_get(v_x_1432_, 0);
lean_inc_ref(v_cs_1433_);
lean_dec_ref(v_x_1432_);
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_array_get_size(v_cs_1433_);
v___x_1436_ = lean_box(0);
v___x_1437_ = lean_nat_dec_lt(v___x_1434_, v___x_1435_);
if (v___x_1437_ == 0)
{
lean_object* v_toApplicative_1438_; lean_object* v_toPure_1439_; lean_object* v___x_1440_; 
lean_dec_ref(v_cs_1433_);
lean_dec(v_f_1431_);
v_toApplicative_1438_ = lean_ctor_get(v_inst_1430_, 0);
lean_inc_ref(v_toApplicative_1438_);
lean_dec_ref(v_inst_1430_);
v_toPure_1439_ = lean_ctor_get(v_toApplicative_1438_, 1);
lean_inc(v_toPure_1439_);
lean_dec_ref(v_toApplicative_1438_);
v___x_1440_ = lean_apply_2(v_toPure_1439_, lean_box(0), v___x_1436_);
return v___x_1440_;
}
else
{
lean_object* v___f_1441_; uint8_t v___x_1442_; 
lean_inc_ref(v_inst_1430_);
v___f_1441_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1441_, 0, v_inst_1430_);
lean_closure_set(v___f_1441_, 1, v_f_1431_);
v___x_1442_ = lean_nat_dec_le(v___x_1435_, v___x_1435_);
if (v___x_1442_ == 0)
{
if (v___x_1437_ == 0)
{
lean_object* v_toApplicative_1443_; lean_object* v_toPure_1444_; lean_object* v___x_1445_; 
lean_dec_ref(v___f_1441_);
lean_dec_ref(v_cs_1433_);
v_toApplicative_1443_ = lean_ctor_get(v_inst_1430_, 0);
lean_inc_ref(v_toApplicative_1443_);
lean_dec_ref(v_inst_1430_);
v_toPure_1444_ = lean_ctor_get(v_toApplicative_1443_, 1);
lean_inc(v_toPure_1444_);
lean_dec_ref(v_toApplicative_1443_);
v___x_1445_ = lean_apply_2(v_toPure_1444_, lean_box(0), v___x_1436_);
return v___x_1445_;
}
else
{
size_t v___x_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
v___x_1446_ = ((size_t)0ULL);
v___x_1447_ = lean_usize_of_nat(v___x_1435_);
v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1430_, v___f_1441_, v_cs_1433_, v___x_1446_, v___x_1447_, v___x_1436_);
return v___x_1448_;
}
}
else
{
size_t v___x_1449_; size_t v___x_1450_; lean_object* v___x_1451_; 
v___x_1449_ = ((size_t)0ULL);
v___x_1450_ = lean_usize_of_nat(v___x_1435_);
v___x_1451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1430_, v___f_1441_, v_cs_1433_, v___x_1449_, v___x_1450_, v___x_1436_);
return v___x_1451_;
}
}
}
else
{
lean_object* v_vs_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_vs_1452_ = lean_ctor_get(v_x_1432_, 0);
lean_inc_ref(v_vs_1452_);
lean_dec_ref(v_x_1432_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_array_get_size(v_vs_1452_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_nat_dec_lt(v___x_1453_, v___x_1454_);
if (v___x_1456_ == 0)
{
lean_object* v_toApplicative_1457_; lean_object* v_toPure_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v_vs_1452_);
lean_dec(v_f_1431_);
v_toApplicative_1457_ = lean_ctor_get(v_inst_1430_, 0);
lean_inc_ref(v_toApplicative_1457_);
lean_dec_ref(v_inst_1430_);
v_toPure_1458_ = lean_ctor_get(v_toApplicative_1457_, 1);
lean_inc(v_toPure_1458_);
lean_dec_ref(v_toApplicative_1457_);
v___x_1459_ = lean_apply_2(v_toPure_1458_, lean_box(0), v___x_1455_);
return v___x_1459_;
}
else
{
lean_object* v___f_1460_; uint8_t v___x_1461_; 
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1460_, 0, v_f_1431_);
v___x_1461_ = lean_nat_dec_le(v___x_1454_, v___x_1454_);
if (v___x_1461_ == 0)
{
if (v___x_1456_ == 0)
{
lean_object* v_toApplicative_1462_; lean_object* v_toPure_1463_; lean_object* v___x_1464_; 
lean_dec_ref(v___f_1460_);
lean_dec_ref(v_vs_1452_);
v_toApplicative_1462_ = lean_ctor_get(v_inst_1430_, 0);
lean_inc_ref(v_toApplicative_1462_);
lean_dec_ref(v_inst_1430_);
v_toPure_1463_ = lean_ctor_get(v_toApplicative_1462_, 1);
lean_inc(v_toPure_1463_);
lean_dec_ref(v_toApplicative_1462_);
v___x_1464_ = lean_apply_2(v_toPure_1463_, lean_box(0), v___x_1455_);
return v___x_1464_;
}
else
{
size_t v___x_1465_; size_t v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = ((size_t)0ULL);
v___x_1466_ = lean_usize_of_nat(v___x_1454_);
v___x_1467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1430_, v___f_1460_, v_vs_1452_, v___x_1465_, v___x_1466_, v___x_1455_);
return v___x_1467_;
}
}
else
{
size_t v___x_1468_; size_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = ((size_t)0ULL);
v___x_1469_ = lean_usize_of_nat(v___x_1454_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1430_, v___f_1460_, v_vs_1452_, v___x_1468_, v___x_1469_, v___x_1455_);
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__0(lean_object* v_inst_1471_, lean_object* v_f_1472_, lean_object* v_x_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1471_, v_f_1472_, v___y_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux(lean_object* v_00_u03b1_1476_, lean_object* v_m_1477_, lean_object* v_inst_1478_, lean_object* v_f_1479_, lean_object* v_x_1480_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1478_, v_f_1479_, v_x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__0(lean_object* v_f_1482_, lean_object* v_x_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_apply_1(v_f_1482_, v___y_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__1(lean_object* v_tail_1486_, lean_object* v_toPure_1487_, lean_object* v_inst_1488_, lean_object* v___f_1489_, lean_object* v_x_1490_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1491_ = lean_unsigned_to_nat(0u);
v___x_1492_ = lean_array_get_size(v_tail_1486_);
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_nat_dec_lt(v___x_1491_, v___x_1492_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; 
lean_dec(v___f_1489_);
lean_dec_ref(v_inst_1488_);
lean_dec_ref(v_tail_1486_);
v___x_1495_ = lean_apply_2(v_toPure_1487_, lean_box(0), v___x_1493_);
return v___x_1495_;
}
else
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_nat_dec_le(v___x_1492_, v___x_1492_);
if (v___x_1496_ == 0)
{
if (v___x_1494_ == 0)
{
lean_object* v___x_1497_; 
lean_dec(v___f_1489_);
lean_dec_ref(v_inst_1488_);
lean_dec_ref(v_tail_1486_);
v___x_1497_ = lean_apply_2(v_toPure_1487_, lean_box(0), v___x_1493_);
return v___x_1497_;
}
else
{
size_t v___x_1498_; size_t v___x_1499_; lean_object* v___x_1500_; 
lean_dec(v_toPure_1487_);
v___x_1498_ = ((size_t)0ULL);
v___x_1499_ = lean_usize_of_nat(v___x_1492_);
v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1488_, v___f_1489_, v_tail_1486_, v___x_1498_, v___x_1499_, v___x_1493_);
return v___x_1500_;
}
}
else
{
size_t v___x_1501_; size_t v___x_1502_; lean_object* v___x_1503_; 
lean_dec(v_toPure_1487_);
v___x_1501_ = ((size_t)0ULL);
v___x_1502_ = lean_usize_of_nat(v___x_1492_);
v___x_1503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1488_, v___f_1489_, v_tail_1486_, v___x_1501_, v___x_1502_, v___x_1493_);
return v___x_1503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg(lean_object* v_inst_1504_, lean_object* v_t_1505_, lean_object* v_f_1506_){
_start:
{
lean_object* v_toApplicative_1507_; lean_object* v_toPure_1508_; lean_object* v_toSeqRight_1509_; lean_object* v_root_1510_; lean_object* v_tail_1511_; lean_object* v___f_1512_; lean_object* v___f_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v_toApplicative_1507_ = lean_ctor_get(v_inst_1504_, 0);
v_toPure_1508_ = lean_ctor_get(v_toApplicative_1507_, 1);
v_toSeqRight_1509_ = lean_ctor_get(v_toApplicative_1507_, 4);
lean_inc(v_toSeqRight_1509_);
v_root_1510_ = lean_ctor_get(v_t_1505_, 0);
lean_inc_ref(v_root_1510_);
v_tail_1511_ = lean_ctor_get(v_t_1505_, 1);
lean_inc_ref(v_tail_1511_);
lean_dec_ref(v_t_1505_);
lean_inc(v_f_1506_);
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1512_, 0, v_f_1506_);
lean_inc_ref(v_inst_1504_);
lean_inc(v_toPure_1508_);
v___f_1513_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1513_, 0, v_tail_1511_);
lean_closure_set(v___f_1513_, 1, v_toPure_1508_);
lean_closure_set(v___f_1513_, 2, v_inst_1504_);
lean_closure_set(v___f_1513_, 3, v___f_1512_);
v___x_1514_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1504_, v_f_1506_, v_root_1510_);
v___x_1515_ = lean_apply_4(v_toSeqRight_1509_, lean_box(0), lean_box(0), v___x_1514_, v___f_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0(lean_object* v_00_u03b1_1516_, lean_object* v_m_1517_, lean_object* v_inst_1518_, lean_object* v_t_1519_, lean_object* v_f_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1518_, v_t_1519_, v_f_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(lean_object* v_j_1522_, lean_object* v_cs_1523_, lean_object* v_toApplicative_1524_, lean_object* v_inst_1525_, lean_object* v___f_1526_, lean_object* v_____r_1527_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; uint8_t v___x_1532_; 
v___x_1528_ = lean_unsigned_to_nat(1u);
v___x_1529_ = lean_nat_add(v_j_1522_, v___x_1528_);
v___x_1530_ = lean_array_get_size(v_cs_1523_);
v___x_1531_ = lean_box(0);
v___x_1532_ = lean_nat_dec_lt(v___x_1529_, v___x_1530_);
if (v___x_1532_ == 0)
{
lean_object* v_toPure_1533_; lean_object* v___x_1534_; 
lean_dec(v___x_1529_);
lean_dec(v___f_1526_);
lean_dec_ref(v_inst_1525_);
lean_dec_ref(v_cs_1523_);
v_toPure_1533_ = lean_ctor_get(v_toApplicative_1524_, 1);
lean_inc(v_toPure_1533_);
lean_dec_ref(v_toApplicative_1524_);
v___x_1534_ = lean_apply_2(v_toPure_1533_, lean_box(0), v___x_1531_);
return v___x_1534_;
}
else
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_nat_dec_le(v___x_1530_, v___x_1530_);
if (v___x_1535_ == 0)
{
if (v___x_1532_ == 0)
{
lean_object* v_toPure_1536_; lean_object* v___x_1537_; 
lean_dec(v___x_1529_);
lean_dec(v___f_1526_);
lean_dec_ref(v_inst_1525_);
lean_dec_ref(v_cs_1523_);
v_toPure_1536_ = lean_ctor_get(v_toApplicative_1524_, 1);
lean_inc(v_toPure_1536_);
lean_dec_ref(v_toApplicative_1524_);
v___x_1537_ = lean_apply_2(v_toPure_1536_, lean_box(0), v___x_1531_);
return v___x_1537_;
}
else
{
size_t v___x_1538_; size_t v___x_1539_; lean_object* v___x_1540_; 
lean_dec_ref(v_toApplicative_1524_);
v___x_1538_ = lean_usize_of_nat(v___x_1529_);
lean_dec(v___x_1529_);
v___x_1539_ = lean_usize_of_nat(v___x_1530_);
v___x_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1525_, v___f_1526_, v_cs_1523_, v___x_1538_, v___x_1539_, v___x_1531_);
return v___x_1540_;
}
}
else
{
size_t v___x_1541_; size_t v___x_1542_; lean_object* v___x_1543_; 
lean_dec_ref(v_toApplicative_1524_);
v___x_1541_ = lean_usize_of_nat(v___x_1529_);
lean_dec(v___x_1529_);
v___x_1542_ = lean_usize_of_nat(v___x_1530_);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1525_, v___f_1526_, v_cs_1523_, v___x_1541_, v___x_1542_, v___x_1531_);
return v___x_1543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed(lean_object* v_j_1544_, lean_object* v_cs_1545_, lean_object* v_toApplicative_1546_, lean_object* v_inst_1547_, lean_object* v___f_1548_, lean_object* v_____r_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(v_j_1544_, v_cs_1545_, v_toApplicative_1546_, v_inst_1547_, v___f_1548_, v_____r_1549_);
lean_dec(v_j_1544_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(lean_object* v_inst_1551_, lean_object* v_f_1552_, lean_object* v_x_1553_, size_t v_x_1554_, size_t v_x_1555_){
_start:
{
if (lean_obj_tag(v_x_1553_) == 0)
{
lean_object* v_toApplicative_1556_; lean_object* v_toBind_1557_; lean_object* v_cs_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; size_t v___x_1561_; lean_object* v_j_1562_; lean_object* v___f_1563_; lean_object* v___x_1564_; size_t v___x_1565_; size_t v___x_1566_; size_t v___x_1567_; size_t v___x_1568_; size_t v___x_1569_; size_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_toApplicative_1556_ = lean_ctor_get(v_inst_1551_, 0);
v_toBind_1557_ = lean_ctor_get(v_inst_1551_, 1);
lean_inc(v_toBind_1557_);
v_cs_1558_ = lean_ctor_get(v_x_1553_, 0);
lean_inc_ref_n(v_cs_1558_, 2);
lean_dec_ref(v_x_1553_);
lean_inc(v_f_1552_);
lean_inc_ref_n(v_inst_1551_, 2);
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1559_, 0, v_inst_1551_);
lean_closure_set(v___f_1559_, 1, v_f_1552_);
v___x_1560_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_1561_ = lean_usize_shift_right(v_x_1554_, v_x_1555_);
v_j_1562_ = lean_usize_to_nat(v___x_1561_);
lean_inc_ref(v_toApplicative_1556_);
lean_inc(v_j_1562_);
v___f_1563_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1563_, 0, v_j_1562_);
lean_closure_set(v___f_1563_, 1, v_cs_1558_);
lean_closure_set(v___f_1563_, 2, v_toApplicative_1556_);
lean_closure_set(v___f_1563_, 3, v_inst_1551_);
lean_closure_set(v___f_1563_, 4, v___f_1559_);
v___x_1564_ = lean_array_get(v___x_1560_, v_cs_1558_, v_j_1562_);
lean_dec(v_j_1562_);
lean_dec_ref(v_cs_1558_);
v___x_1565_ = ((size_t)1ULL);
v___x_1566_ = lean_usize_shift_left(v___x_1565_, v_x_1555_);
v___x_1567_ = lean_usize_sub(v___x_1566_, v___x_1565_);
v___x_1568_ = lean_usize_land(v_x_1554_, v___x_1567_);
v___x_1569_ = ((size_t)5ULL);
v___x_1570_ = lean_usize_sub(v_x_1555_, v___x_1569_);
v___x_1571_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1551_, v_f_1552_, v___x_1564_, v___x_1568_, v___x_1570_);
v___x_1572_ = lean_apply_4(v_toBind_1557_, lean_box(0), lean_box(0), v___x_1571_, v___f_1563_);
return v___x_1572_;
}
else
{
lean_object* v_toApplicative_1573_; lean_object* v_vs_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; uint8_t v___x_1578_; 
v_toApplicative_1573_ = lean_ctor_get(v_inst_1551_, 0);
v_vs_1574_ = lean_ctor_get(v_x_1553_, 0);
lean_inc_ref(v_vs_1574_);
lean_dec_ref(v_x_1553_);
v___x_1575_ = lean_usize_to_nat(v_x_1554_);
v___x_1576_ = lean_array_get_size(v_vs_1574_);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_nat_dec_lt(v___x_1575_, v___x_1576_);
if (v___x_1578_ == 0)
{
lean_object* v_toPure_1579_; lean_object* v___x_1580_; 
lean_inc_ref(v_toApplicative_1573_);
lean_dec(v___x_1575_);
lean_dec_ref(v_vs_1574_);
lean_dec(v_f_1552_);
lean_dec_ref(v_inst_1551_);
v_toPure_1579_ = lean_ctor_get(v_toApplicative_1573_, 1);
lean_inc(v_toPure_1579_);
lean_dec_ref(v_toApplicative_1573_);
v___x_1580_ = lean_apply_2(v_toPure_1579_, lean_box(0), v___x_1577_);
return v___x_1580_;
}
else
{
lean_object* v___f_1581_; uint8_t v___x_1582_; 
v___f_1581_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1581_, 0, v_f_1552_);
v___x_1582_ = lean_nat_dec_le(v___x_1576_, v___x_1576_);
if (v___x_1582_ == 0)
{
if (v___x_1578_ == 0)
{
lean_object* v_toPure_1583_; lean_object* v___x_1584_; 
lean_inc_ref(v_toApplicative_1573_);
lean_dec_ref(v___f_1581_);
lean_dec(v___x_1575_);
lean_dec_ref(v_vs_1574_);
lean_dec_ref(v_inst_1551_);
v_toPure_1583_ = lean_ctor_get(v_toApplicative_1573_, 1);
lean_inc(v_toPure_1583_);
lean_dec_ref(v_toApplicative_1573_);
v___x_1584_ = lean_apply_2(v_toPure_1583_, lean_box(0), v___x_1577_);
return v___x_1584_;
}
else
{
size_t v___x_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v___x_1585_ = lean_usize_of_nat(v___x_1575_);
lean_dec(v___x_1575_);
v___x_1586_ = lean_usize_of_nat(v___x_1576_);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1551_, v___f_1581_, v_vs_1574_, v___x_1585_, v___x_1586_, v___x_1577_);
return v___x_1587_;
}
}
else
{
size_t v___x_1588_; size_t v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = lean_usize_of_nat(v___x_1575_);
lean_dec(v___x_1575_);
v___x_1589_ = lean_usize_of_nat(v___x_1576_);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1551_, v___f_1581_, v_vs_1574_, v___x_1588_, v___x_1589_, v___x_1577_);
return v___x_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___boxed(lean_object* v_inst_1591_, lean_object* v_f_1592_, lean_object* v_x_1593_, lean_object* v_x_1594_, lean_object* v_x_1595_){
_start:
{
size_t v_x_290__boxed_1596_; size_t v_x_291__boxed_1597_; lean_object* v_res_1598_; 
v_x_290__boxed_1596_ = lean_unbox_usize(v_x_1594_);
lean_dec(v_x_1594_);
v_x_291__boxed_1597_ = lean_unbox_usize(v_x_1595_);
lean_dec(v_x_1595_);
v_res_1598_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1591_, v_f_1592_, v_x_1593_, v_x_290__boxed_1596_, v_x_291__boxed_1597_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(lean_object* v_00_u03b1_1599_, lean_object* v_m_1600_, lean_object* v_inst_1601_, lean_object* v_f_1602_, lean_object* v_x_1603_, size_t v_x_1604_, size_t v_x_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1601_, v_f_1602_, v_x_1603_, v_x_1604_, v_x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___boxed(lean_object* v_00_u03b1_1607_, lean_object* v_m_1608_, lean_object* v_inst_1609_, lean_object* v_f_1610_, lean_object* v_x_1611_, lean_object* v_x_1612_, lean_object* v_x_1613_){
_start:
{
size_t v_x_360__boxed_1614_; size_t v_x_361__boxed_1615_; lean_object* v_res_1616_; 
v_x_360__boxed_1614_ = lean_unbox_usize(v_x_1612_);
lean_dec(v_x_1612_);
v_x_361__boxed_1615_ = lean_unbox_usize(v_x_1613_);
lean_dec(v_x_1613_);
v_res_1616_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(v_00_u03b1_1607_, v_m_1608_, v_inst_1609_, v_f_1610_, v_x_1611_, v_x_360__boxed_1614_, v_x_361__boxed_1615_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1(lean_object* v_tail_1617_, lean_object* v___x_1618_, lean_object* v_toApplicative_1619_, lean_object* v_inst_1620_, lean_object* v___f_1621_, lean_object* v_____r_1622_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v___x_1623_ = lean_array_get_size(v_tail_1617_);
v___x_1624_ = lean_box(0);
v___x_1625_ = lean_nat_dec_lt(v___x_1618_, v___x_1623_);
if (v___x_1625_ == 0)
{
lean_object* v_toPure_1626_; lean_object* v___x_1627_; 
lean_dec(v___f_1621_);
lean_dec_ref(v_inst_1620_);
lean_dec_ref(v_tail_1617_);
v_toPure_1626_ = lean_ctor_get(v_toApplicative_1619_, 1);
lean_inc(v_toPure_1626_);
lean_dec_ref(v_toApplicative_1619_);
v___x_1627_ = lean_apply_2(v_toPure_1626_, lean_box(0), v___x_1624_);
return v___x_1627_;
}
else
{
uint8_t v___x_1628_; 
v___x_1628_ = lean_nat_dec_le(v___x_1623_, v___x_1623_);
if (v___x_1628_ == 0)
{
if (v___x_1625_ == 0)
{
lean_object* v_toPure_1629_; lean_object* v___x_1630_; 
lean_dec(v___f_1621_);
lean_dec_ref(v_inst_1620_);
lean_dec_ref(v_tail_1617_);
v_toPure_1629_ = lean_ctor_get(v_toApplicative_1619_, 1);
lean_inc(v_toPure_1629_);
lean_dec_ref(v_toApplicative_1619_);
v___x_1630_ = lean_apply_2(v_toPure_1629_, lean_box(0), v___x_1624_);
return v___x_1630_;
}
else
{
size_t v___x_1631_; size_t v___x_1632_; lean_object* v___x_1633_; 
lean_dec_ref(v_toApplicative_1619_);
v___x_1631_ = ((size_t)0ULL);
v___x_1632_ = lean_usize_of_nat(v___x_1623_);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1620_, v___f_1621_, v_tail_1617_, v___x_1631_, v___x_1632_, v___x_1624_);
return v___x_1633_;
}
}
else
{
size_t v___x_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref(v_toApplicative_1619_);
v___x_1634_ = ((size_t)0ULL);
v___x_1635_ = lean_usize_of_nat(v___x_1623_);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1620_, v___f_1621_, v_tail_1617_, v___x_1634_, v___x_1635_, v___x_1624_);
return v___x_1636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1___boxed(lean_object* v_tail_1637_, lean_object* v___x_1638_, lean_object* v_toApplicative_1639_, lean_object* v_inst_1640_, lean_object* v___f_1641_, lean_object* v_____r_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_PersistentArray_forM___redArg___lam__1(v_tail_1637_, v___x_1638_, v_toApplicative_1639_, v_inst_1640_, v___f_1641_, v_____r_1642_);
lean_dec(v___x_1638_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg(lean_object* v_inst_1644_, lean_object* v_t_1645_, lean_object* v_f_1646_, lean_object* v_start_1647_){
_start:
{
lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v___x_1649_ = lean_nat_dec_eq(v_start_1647_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v_root_1650_; lean_object* v_tail_1651_; size_t v_shift_1652_; lean_object* v_tailOff_1653_; uint8_t v___x_1654_; 
v_root_1650_ = lean_ctor_get(v_t_1645_, 0);
lean_inc_ref(v_root_1650_);
v_tail_1651_ = lean_ctor_get(v_t_1645_, 1);
lean_inc_ref(v_tail_1651_);
v_shift_1652_ = lean_ctor_get_usize(v_t_1645_, 4);
v_tailOff_1653_ = lean_ctor_get(v_t_1645_, 3);
lean_inc(v_tailOff_1653_);
lean_dec_ref(v_t_1645_);
v___x_1654_ = lean_nat_dec_le(v_tailOff_1653_, v_start_1647_);
if (v___x_1654_ == 0)
{
lean_object* v_toApplicative_1655_; lean_object* v_toBind_1656_; lean_object* v___f_1657_; lean_object* v___f_1658_; size_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
lean_dec(v_tailOff_1653_);
v_toApplicative_1655_ = lean_ctor_get(v_inst_1644_, 0);
v_toBind_1656_ = lean_ctor_get(v_inst_1644_, 1);
lean_inc(v_toBind_1656_);
lean_inc(v_f_1646_);
v___f_1657_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1657_, 0, v_f_1646_);
lean_inc_ref(v_inst_1644_);
lean_inc_ref(v_toApplicative_1655_);
v___f_1658_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1658_, 0, v_tail_1651_);
lean_closure_set(v___f_1658_, 1, v___x_1648_);
lean_closure_set(v___f_1658_, 2, v_toApplicative_1655_);
lean_closure_set(v___f_1658_, 3, v_inst_1644_);
lean_closure_set(v___f_1658_, 4, v___f_1657_);
v___x_1659_ = lean_usize_of_nat(v_start_1647_);
v___x_1660_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1644_, v_f_1646_, v_root_1650_, v___x_1659_, v_shift_1652_);
v___x_1661_ = lean_apply_4(v_toBind_1656_, lean_box(0), lean_box(0), v___x_1660_, v___f_1658_);
return v___x_1661_;
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
lean_dec_ref(v_root_1650_);
v___x_1662_ = lean_nat_sub(v_start_1647_, v_tailOff_1653_);
lean_dec(v_tailOff_1653_);
v___x_1663_ = lean_array_get_size(v_tail_1651_);
v___x_1664_ = lean_box(0);
v___x_1665_ = lean_nat_dec_lt(v___x_1662_, v___x_1663_);
if (v___x_1665_ == 0)
{
lean_object* v_toApplicative_1666_; lean_object* v_toPure_1667_; lean_object* v___x_1668_; 
lean_dec(v___x_1662_);
lean_dec_ref(v_tail_1651_);
lean_dec(v_f_1646_);
v_toApplicative_1666_ = lean_ctor_get(v_inst_1644_, 0);
lean_inc_ref(v_toApplicative_1666_);
lean_dec_ref(v_inst_1644_);
v_toPure_1667_ = lean_ctor_get(v_toApplicative_1666_, 1);
lean_inc(v_toPure_1667_);
lean_dec_ref(v_toApplicative_1666_);
v___x_1668_ = lean_apply_2(v_toPure_1667_, lean_box(0), v___x_1664_);
return v___x_1668_;
}
else
{
lean_object* v___f_1669_; uint8_t v___x_1670_; 
v___f_1669_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1669_, 0, v_f_1646_);
v___x_1670_ = lean_nat_dec_le(v___x_1663_, v___x_1663_);
if (v___x_1670_ == 0)
{
if (v___x_1665_ == 0)
{
lean_object* v_toApplicative_1671_; lean_object* v_toPure_1672_; lean_object* v___x_1673_; 
lean_dec_ref(v___f_1669_);
lean_dec(v___x_1662_);
lean_dec_ref(v_tail_1651_);
v_toApplicative_1671_ = lean_ctor_get(v_inst_1644_, 0);
lean_inc_ref(v_toApplicative_1671_);
lean_dec_ref(v_inst_1644_);
v_toPure_1672_ = lean_ctor_get(v_toApplicative_1671_, 1);
lean_inc(v_toPure_1672_);
lean_dec_ref(v_toApplicative_1671_);
v___x_1673_ = lean_apply_2(v_toPure_1672_, lean_box(0), v___x_1664_);
return v___x_1673_;
}
else
{
size_t v___x_1674_; size_t v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_usize_of_nat(v___x_1662_);
lean_dec(v___x_1662_);
v___x_1675_ = lean_usize_of_nat(v___x_1663_);
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1644_, v___f_1669_, v_tail_1651_, v___x_1674_, v___x_1675_, v___x_1664_);
return v___x_1676_;
}
}
else
{
size_t v___x_1677_; size_t v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_usize_of_nat(v___x_1662_);
lean_dec(v___x_1662_);
v___x_1678_ = lean_usize_of_nat(v___x_1663_);
v___x_1679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1644_, v___f_1669_, v_tail_1651_, v___x_1677_, v___x_1678_, v___x_1664_);
return v___x_1679_;
}
}
}
}
else
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1644_, v_t_1645_, v_f_1646_);
return v___x_1680_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___boxed(lean_object* v_inst_1681_, lean_object* v_t_1682_, lean_object* v_f_1683_, lean_object* v_start_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_PersistentArray_forM___redArg(v_inst_1681_, v_t_1682_, v_f_1683_, v_start_1684_);
lean_dec(v_start_1684_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM(lean_object* v_00_u03b1_1686_, lean_object* v_m_1687_, lean_object* v_inst_1688_, lean_object* v_t_1689_, lean_object* v_f_1690_, lean_object* v_start_1691_){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_PersistentArray_forM___redArg(v_inst_1688_, v_t_1689_, v_f_1690_, v_start_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___boxed(lean_object* v_00_u03b1_1693_, lean_object* v_m_1694_, lean_object* v_inst_1695_, lean_object* v_t_1696_, lean_object* v_f_1697_, lean_object* v_start_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lean_PersistentArray_forM(v_00_u03b1_1693_, v_m_1694_, v_inst_1695_, v_t_1696_, v_f_1697_, v_start_1698_);
lean_dec(v_start_1698_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___lam__0(lean_object* v_f_1700_, lean_object* v_x1_1701_, lean_object* v_x2_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_apply_2(v_f_1700_, v_x1_1701_, v_x2_1702_);
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg(lean_object* v_t_1723_, lean_object* v_f_1724_, lean_object* v_init_1725_, lean_object* v_start_1726_){
_start:
{
lean_object* v___f_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___f_1727_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1727_, 0, v_f_1724_);
v___x_1728_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1729_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1728_, v_t_1723_, v___f_1727_, v_init_1725_, v_start_1726_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___boxed(lean_object* v_t_1730_, lean_object* v_f_1731_, lean_object* v_init_1732_, lean_object* v_start_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_PersistentArray_foldl___redArg(v_t_1730_, v_f_1731_, v_init_1732_, v_start_1733_);
lean_dec(v_start_1733_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl(lean_object* v_00_u03b1_1735_, lean_object* v_00_u03b2_1736_, lean_object* v_t_1737_, lean_object* v_f_1738_, lean_object* v_init_1739_, lean_object* v_start_1740_){
_start:
{
lean_object* v___f_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___f_1741_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1741_, 0, v_f_1738_);
v___x_1742_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1743_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1742_, v_t_1737_, v___f_1741_, v_init_1739_, v_start_1740_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___boxed(lean_object* v_00_u03b1_1744_, lean_object* v_00_u03b2_1745_, lean_object* v_t_1746_, lean_object* v_f_1747_, lean_object* v_init_1748_, lean_object* v_start_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_PersistentArray_foldl(v_00_u03b1_1744_, v_00_u03b2_1745_, v_t_1746_, v_f_1747_, v_init_1748_, v_start_1749_);
lean_dec(v_start_1749_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr___redArg(lean_object* v_t_1751_, lean_object* v_f_1752_, lean_object* v_init_1753_){
_start:
{
lean_object* v___f_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___f_1754_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1754_, 0, v_f_1752_);
v___x_1755_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1756_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1755_, v_t_1751_, v___f_1754_, v_init_1753_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr(lean_object* v_00_u03b1_1757_, lean_object* v_00_u03b2_1758_, lean_object* v_t_1759_, lean_object* v_f_1760_, lean_object* v_init_1761_){
_start:
{
lean_object* v___f_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___f_1762_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1762_, 0, v_f_1760_);
v___x_1763_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1764_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1763_, v_t_1759_, v___f_1762_, v_init_1761_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg___lam__0(lean_object* v_p_1765_, lean_object* v_x1_1766_, lean_object* v_x2_1767_){
_start:
{
lean_object* v___x_1768_; uint8_t v___x_1769_; 
lean_inc(v_x2_1767_);
v___x_1768_ = lean_apply_1(v_p_1765_, v_x2_1767_);
v___x_1769_ = lean_unbox(v___x_1768_);
if (v___x_1769_ == 0)
{
lean_dec(v_x2_1767_);
return v_x1_1766_;
}
else
{
lean_object* v___x_1770_; 
v___x_1770_ = l_Lean_PersistentArray_push___redArg(v_x1_1766_, v_x2_1767_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg(lean_object* v_as_1771_, lean_object* v_p_1772_){
_start:
{
lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___f_1773_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1773_, 0, v_p_1772_);
v___x_1774_ = lean_unsigned_to_nat(32u);
v___x_1775_ = lean_mk_empty_array_with_capacity(v___x_1774_);
lean_dec_ref(v___x_1775_);
v___x_1776_ = lean_unsigned_to_nat(0u);
v___x_1777_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
v___x_1778_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1779_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1778_, v_as_1771_, v___f_1773_, v___x_1777_, v___x_1776_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter(lean_object* v_00_u03b1_1780_, lean_object* v_as_1781_, lean_object* v_p_1782_){
_start:
{
lean_object* v___f_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___f_1783_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1783_, 0, v_p_1782_);
v___x_1784_ = lean_unsigned_to_nat(32u);
v___x_1785_ = lean_mk_empty_array_with_capacity(v___x_1784_);
lean_dec_ref(v___x_1785_);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
v___x_1788_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1789_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1788_, v_as_1781_, v___f_1783_, v___x_1787_, v___x_1786_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(lean_object* v_as_1790_, size_t v_i_1791_, size_t v_stop_1792_, lean_object* v_b_1793_){
_start:
{
uint8_t v___x_1794_; 
v___x_1794_ = lean_usize_dec_eq(v_i_1791_, v_stop_1792_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; size_t v___x_1797_; size_t v___x_1798_; 
v___x_1795_ = lean_array_uget_borrowed(v_as_1790_, v_i_1791_);
lean_inc(v___x_1795_);
v___x_1796_ = lean_array_push(v_b_1793_, v___x_1795_);
v___x_1797_ = ((size_t)1ULL);
v___x_1798_ = lean_usize_add(v_i_1791_, v___x_1797_);
v_i_1791_ = v___x_1798_;
v_b_1793_ = v___x_1796_;
goto _start;
}
else
{
return v_b_1793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg___boxed(lean_object* v_as_1800_, lean_object* v_i_1801_, lean_object* v_stop_1802_, lean_object* v_b_1803_){
_start:
{
size_t v_i_boxed_1804_; size_t v_stop_boxed_1805_; lean_object* v_res_1806_; 
v_i_boxed_1804_ = lean_unbox_usize(v_i_1801_);
lean_dec(v_i_1801_);
v_stop_boxed_1805_ = lean_unbox_usize(v_stop_1802_);
lean_dec(v_stop_1802_);
v_res_1806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1800_, v_i_boxed_1804_, v_stop_boxed_1805_, v_b_1803_);
lean_dec_ref(v_as_1800_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(lean_object* v_x_1807_, lean_object* v_x_1808_){
_start:
{
if (lean_obj_tag(v_x_1807_) == 0)
{
lean_object* v_cs_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v_cs_1809_ = lean_ctor_get(v_x_1807_, 0);
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = lean_array_get_size(v_cs_1809_);
v___x_1812_ = lean_nat_dec_lt(v___x_1810_, v___x_1811_);
if (v___x_1812_ == 0)
{
return v_x_1808_;
}
else
{
uint8_t v___x_1813_; 
v___x_1813_ = lean_nat_dec_le(v___x_1811_, v___x_1811_);
if (v___x_1813_ == 0)
{
if (v___x_1812_ == 0)
{
return v_x_1808_;
}
else
{
size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = ((size_t)0ULL);
v___x_1815_ = lean_usize_of_nat(v___x_1811_);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1809_, v___x_1814_, v___x_1815_, v_x_1808_);
return v___x_1816_;
}
}
else
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = lean_usize_of_nat(v___x_1811_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1809_, v___x_1817_, v___x_1818_, v_x_1808_);
return v___x_1819_;
}
}
}
else
{
lean_object* v_vs_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; 
v_vs_1820_ = lean_ctor_get(v_x_1807_, 0);
v___x_1821_ = lean_unsigned_to_nat(0u);
v___x_1822_ = lean_array_get_size(v_vs_1820_);
v___x_1823_ = lean_nat_dec_lt(v___x_1821_, v___x_1822_);
if (v___x_1823_ == 0)
{
return v_x_1808_;
}
else
{
uint8_t v___x_1824_; 
v___x_1824_ = lean_nat_dec_le(v___x_1822_, v___x_1822_);
if (v___x_1824_ == 0)
{
if (v___x_1823_ == 0)
{
return v_x_1808_;
}
else
{
size_t v___x_1825_; size_t v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = ((size_t)0ULL);
v___x_1826_ = lean_usize_of_nat(v___x_1822_);
v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1820_, v___x_1825_, v___x_1826_, v_x_1808_);
return v___x_1827_;
}
}
else
{
size_t v___x_1828_; size_t v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = ((size_t)0ULL);
v___x_1829_ = lean_usize_of_nat(v___x_1822_);
v___x_1830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1820_, v___x_1828_, v___x_1829_, v_x_1808_);
return v___x_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(lean_object* v_as_1831_, size_t v_i_1832_, size_t v_stop_1833_, lean_object* v_b_1834_){
_start:
{
uint8_t v___x_1835_; 
v___x_1835_ = lean_usize_dec_eq(v_i_1832_, v_stop_1833_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; lean_object* v___x_1837_; size_t v___x_1838_; size_t v___x_1839_; 
v___x_1836_ = lean_array_uget_borrowed(v_as_1831_, v_i_1832_);
v___x_1837_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v___x_1836_, v_b_1834_);
v___x_1838_ = ((size_t)1ULL);
v___x_1839_ = lean_usize_add(v_i_1832_, v___x_1838_);
v_i_1832_ = v___x_1839_;
v_b_1834_ = v___x_1837_;
goto _start;
}
else
{
return v_b_1834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_1841_, lean_object* v_i_1842_, lean_object* v_stop_1843_, lean_object* v_b_1844_){
_start:
{
size_t v_i_boxed_1845_; size_t v_stop_boxed_1846_; lean_object* v_res_1847_; 
v_i_boxed_1845_ = lean_unbox_usize(v_i_1842_);
lean_dec(v_i_1842_);
v_stop_boxed_1846_ = lean_unbox_usize(v_stop_1843_);
lean_dec(v_stop_1843_);
v_res_1847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1841_, v_i_boxed_1845_, v_stop_boxed_1846_, v_b_1844_);
lean_dec_ref(v_as_1841_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(lean_object* v_x_1848_, lean_object* v_x_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1848_, v_x_1849_);
lean_dec_ref(v_x_1848_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(lean_object* v_x_1851_, size_t v_x_1852_, size_t v_x_1853_, lean_object* v_x_1854_){
_start:
{
if (lean_obj_tag(v_x_1851_) == 0)
{
lean_object* v_cs_1855_; lean_object* v___x_1856_; size_t v___x_1857_; lean_object* v_j_1858_; lean_object* v___x_1859_; size_t v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; size_t v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v_cs_1855_ = lean_ctor_get(v_x_1851_, 0);
v___x_1856_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_1857_ = lean_usize_shift_right(v_x_1852_, v_x_1853_);
v_j_1858_ = lean_usize_to_nat(v___x_1857_);
v___x_1859_ = lean_array_get_borrowed(v___x_1856_, v_cs_1855_, v_j_1858_);
v___x_1860_ = ((size_t)1ULL);
v___x_1861_ = lean_usize_shift_left(v___x_1860_, v_x_1853_);
v___x_1862_ = lean_usize_sub(v___x_1861_, v___x_1860_);
v___x_1863_ = lean_usize_land(v_x_1852_, v___x_1862_);
v___x_1864_ = ((size_t)5ULL);
v___x_1865_ = lean_usize_sub(v_x_1853_, v___x_1864_);
v___x_1866_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v___x_1859_, v___x_1863_, v___x_1865_, v_x_1854_);
v___x_1867_ = lean_unsigned_to_nat(1u);
v___x_1868_ = lean_nat_add(v_j_1858_, v___x_1867_);
lean_dec(v_j_1858_);
v___x_1869_ = lean_array_get_size(v_cs_1855_);
v___x_1870_ = lean_nat_dec_lt(v___x_1868_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_dec(v___x_1868_);
return v___x_1866_;
}
else
{
uint8_t v___x_1871_; 
v___x_1871_ = lean_nat_dec_le(v___x_1869_, v___x_1869_);
if (v___x_1871_ == 0)
{
if (v___x_1870_ == 0)
{
lean_dec(v___x_1868_);
return v___x_1866_;
}
else
{
size_t v___x_1872_; size_t v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = lean_usize_of_nat(v___x_1868_);
lean_dec(v___x_1868_);
v___x_1873_ = lean_usize_of_nat(v___x_1869_);
v___x_1874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1855_, v___x_1872_, v___x_1873_, v___x_1866_);
return v___x_1874_;
}
}
else
{
size_t v___x_1875_; size_t v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_usize_of_nat(v___x_1868_);
lean_dec(v___x_1868_);
v___x_1876_ = lean_usize_of_nat(v___x_1869_);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1855_, v___x_1875_, v___x_1876_, v___x_1866_);
return v___x_1877_;
}
}
}
else
{
lean_object* v_vs_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; 
v_vs_1878_ = lean_ctor_get(v_x_1851_, 0);
v___x_1879_ = lean_usize_to_nat(v_x_1852_);
v___x_1880_ = lean_array_get_size(v_vs_1878_);
v___x_1881_ = lean_nat_dec_lt(v___x_1879_, v___x_1880_);
if (v___x_1881_ == 0)
{
lean_dec(v___x_1879_);
return v_x_1854_;
}
else
{
uint8_t v___x_1882_; 
v___x_1882_ = lean_nat_dec_le(v___x_1880_, v___x_1880_);
if (v___x_1882_ == 0)
{
if (v___x_1881_ == 0)
{
lean_dec(v___x_1879_);
return v_x_1854_;
}
else
{
size_t v___x_1883_; size_t v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_usize_of_nat(v___x_1879_);
lean_dec(v___x_1879_);
v___x_1884_ = lean_usize_of_nat(v___x_1880_);
v___x_1885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1878_, v___x_1883_, v___x_1884_, v_x_1854_);
return v___x_1885_;
}
}
else
{
size_t v___x_1886_; size_t v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = lean_usize_of_nat(v___x_1879_);
lean_dec(v___x_1879_);
v___x_1887_ = lean_usize_of_nat(v___x_1880_);
v___x_1888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1878_, v___x_1886_, v___x_1887_, v_x_1854_);
return v___x_1888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
size_t v_x_1497__boxed_1893_; size_t v_x_1498__boxed_1894_; lean_object* v_res_1895_; 
v_x_1497__boxed_1893_ = lean_unbox_usize(v_x_1890_);
lean_dec(v_x_1890_);
v_x_1498__boxed_1894_ = lean_unbox_usize(v_x_1891_);
lean_dec(v_x_1891_);
v_res_1895_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1889_, v_x_1497__boxed_1893_, v_x_1498__boxed_1894_, v_x_1892_);
lean_dec_ref(v_x_1889_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(lean_object* v_t_1896_, lean_object* v_init_1897_, lean_object* v_start_1898_){
_start:
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_nat_dec_eq(v_start_1898_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v_root_1901_; lean_object* v_tail_1902_; size_t v_shift_1903_; lean_object* v_tailOff_1904_; uint8_t v___x_1905_; 
v_root_1901_ = lean_ctor_get(v_t_1896_, 0);
v_tail_1902_ = lean_ctor_get(v_t_1896_, 1);
v_shift_1903_ = lean_ctor_get_usize(v_t_1896_, 4);
v_tailOff_1904_ = lean_ctor_get(v_t_1896_, 3);
v___x_1905_ = lean_nat_dec_le(v_tailOff_1904_, v_start_1898_);
if (v___x_1905_ == 0)
{
size_t v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1906_ = lean_usize_of_nat(v_start_1898_);
v___x_1907_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_root_1901_, v___x_1906_, v_shift_1903_, v_init_1897_);
v___x_1908_ = lean_array_get_size(v_tail_1902_);
v___x_1909_ = lean_nat_dec_lt(v___x_1899_, v___x_1908_);
if (v___x_1909_ == 0)
{
return v___x_1907_;
}
else
{
uint8_t v___x_1910_; 
v___x_1910_ = lean_nat_dec_le(v___x_1908_, v___x_1908_);
if (v___x_1910_ == 0)
{
if (v___x_1909_ == 0)
{
return v___x_1907_;
}
else
{
size_t v___x_1911_; size_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = ((size_t)0ULL);
v___x_1912_ = lean_usize_of_nat(v___x_1908_);
v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1902_, v___x_1911_, v___x_1912_, v___x_1907_);
return v___x_1913_;
}
}
else
{
size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = lean_usize_of_nat(v___x_1908_);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1902_, v___x_1914_, v___x_1915_, v___x_1907_);
return v___x_1916_;
}
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; uint8_t v___x_1919_; 
v___x_1917_ = lean_nat_sub(v_start_1898_, v_tailOff_1904_);
v___x_1918_ = lean_array_get_size(v_tail_1902_);
v___x_1919_ = lean_nat_dec_lt(v___x_1917_, v___x_1918_);
if (v___x_1919_ == 0)
{
lean_dec(v___x_1917_);
return v_init_1897_;
}
else
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_nat_dec_le(v___x_1918_, v___x_1918_);
if (v___x_1920_ == 0)
{
if (v___x_1919_ == 0)
{
lean_dec(v___x_1917_);
return v_init_1897_;
}
else
{
size_t v___x_1921_; size_t v___x_1922_; lean_object* v___x_1923_; 
v___x_1921_ = lean_usize_of_nat(v___x_1917_);
lean_dec(v___x_1917_);
v___x_1922_ = lean_usize_of_nat(v___x_1918_);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1902_, v___x_1921_, v___x_1922_, v_init_1897_);
return v___x_1923_;
}
}
else
{
size_t v___x_1924_; size_t v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = lean_usize_of_nat(v___x_1917_);
lean_dec(v___x_1917_);
v___x_1925_ = lean_usize_of_nat(v___x_1918_);
v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1902_, v___x_1924_, v___x_1925_, v_init_1897_);
return v___x_1926_;
}
}
}
}
else
{
lean_object* v_root_1927_; lean_object* v_tail_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v_root_1927_ = lean_ctor_get(v_t_1896_, 0);
v_tail_1928_ = lean_ctor_get(v_t_1896_, 1);
v___x_1929_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_root_1927_, v_init_1897_);
v___x_1930_ = lean_array_get_size(v_tail_1928_);
v___x_1931_ = lean_nat_dec_lt(v___x_1899_, v___x_1930_);
if (v___x_1931_ == 0)
{
return v___x_1929_;
}
else
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_nat_dec_le(v___x_1930_, v___x_1930_);
if (v___x_1932_ == 0)
{
if (v___x_1931_ == 0)
{
return v___x_1929_;
}
else
{
size_t v___x_1933_; size_t v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = ((size_t)0ULL);
v___x_1934_ = lean_usize_of_nat(v___x_1930_);
v___x_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1928_, v___x_1933_, v___x_1934_, v___x_1929_);
return v___x_1935_;
}
}
else
{
size_t v___x_1936_; size_t v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = ((size_t)0ULL);
v___x_1937_ = lean_usize_of_nat(v___x_1930_);
v___x_1938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1928_, v___x_1936_, v___x_1937_, v___x_1929_);
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(lean_object* v_t_1939_, lean_object* v_init_1940_, lean_object* v_start_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1939_, v_init_1940_, v_start_1941_);
lean_dec(v_start_1941_);
lean_dec_ref(v_t_1939_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object* v_t_1943_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1944_ = lean_unsigned_to_nat(0u);
v___x_1945_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
v___x_1946_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1943_, v___x_1945_, v___x_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg___boxed(lean_object* v_t_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_PersistentArray_toArray___redArg(v_t_1947_);
lean_dec_ref(v_t_1947_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray(lean_object* v_00_u03b1_1949_, lean_object* v_t_1950_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_PersistentArray_toArray___redArg(v_t_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_t_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_PersistentArray_toArray(v_00_u03b1_1952_, v_t_1953_);
lean_dec_ref(v_t_1953_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(lean_object* v_00_u03b1_1955_, lean_object* v_t_1956_, lean_object* v_init_1957_, lean_object* v_start_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1956_, v_init_1957_, v_start_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(lean_object* v_00_u03b1_1960_, lean_object* v_t_1961_, lean_object* v_init_1962_, lean_object* v_start_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(v_00_u03b1_1960_, v_t_1961_, v_init_1962_, v_start_1963_);
lean_dec(v_start_1963_);
lean_dec_ref(v_t_1961_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(lean_object* v_00_u03b1_1965_, lean_object* v_x_1966_, size_t v_x_1967_, size_t v_x_1968_, lean_object* v_x_1969_){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1966_, v_x_1967_, v_x_1968_, v_x_1969_);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1971_, lean_object* v_x_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_, lean_object* v_x_1975_){
_start:
{
size_t v_x_1655__boxed_1976_; size_t v_x_1656__boxed_1977_; lean_object* v_res_1978_; 
v_x_1655__boxed_1976_ = lean_unbox_usize(v_x_1973_);
lean_dec(v_x_1973_);
v_x_1656__boxed_1977_ = lean_unbox_usize(v_x_1974_);
lean_dec(v_x_1974_);
v_res_1978_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(v_00_u03b1_1971_, v_x_1972_, v_x_1655__boxed_1976_, v_x_1656__boxed_1977_, v_x_1975_);
lean_dec_ref(v_x_1972_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(lean_object* v_00_u03b1_1979_, lean_object* v_as_1980_, size_t v_i_1981_, size_t v_stop_1982_, lean_object* v_b_1983_){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1980_, v_i_1981_, v_stop_1982_, v_b_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1985_, lean_object* v_as_1986_, lean_object* v_i_1987_, lean_object* v_stop_1988_, lean_object* v_b_1989_){
_start:
{
size_t v_i_boxed_1990_; size_t v_stop_boxed_1991_; lean_object* v_res_1992_; 
v_i_boxed_1990_ = lean_unbox_usize(v_i_1987_);
lean_dec(v_i_1987_);
v_stop_boxed_1991_ = lean_unbox_usize(v_stop_1988_);
lean_dec(v_stop_1988_);
v_res_1992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(v_00_u03b1_1985_, v_as_1986_, v_i_boxed_1990_, v_stop_boxed_1991_, v_b_1989_);
lean_dec_ref(v_as_1986_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(lean_object* v_00_u03b1_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
lean_object* v___x_1996_; 
v___x_1996_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1994_, v_x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1997_, lean_object* v_x_1998_, lean_object* v_x_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(v_00_u03b1_1997_, v_x_1998_, v_x_1999_);
lean_dec_ref(v_x_1998_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2001_, lean_object* v_as_2002_, size_t v_i_2003_, size_t v_stop_2004_, lean_object* v_b_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_2002_, v_i_2003_, v_stop_2004_, v_b_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2007_, lean_object* v_as_2008_, lean_object* v_i_2009_, lean_object* v_stop_2010_, lean_object* v_b_2011_){
_start:
{
size_t v_i_boxed_2012_; size_t v_stop_boxed_2013_; lean_object* v_res_2014_; 
v_i_boxed_2012_ = lean_unbox_usize(v_i_2009_);
lean_dec(v_i_2009_);
v_stop_boxed_2013_ = lean_unbox_usize(v_stop_2010_);
lean_dec(v_stop_2010_);
v_res_2014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(v_00_u03b1_2007_, v_as_2008_, v_i_boxed_2012_, v_stop_boxed_2013_, v_b_2011_);
lean_dec_ref(v_as_2008_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(lean_object* v_as_2015_, size_t v_i_2016_, size_t v_stop_2017_, lean_object* v_b_2018_){
_start:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_usize_dec_eq(v_i_2016_, v_stop_2017_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; size_t v___x_2022_; size_t v___x_2023_; 
v___x_2020_ = lean_array_uget_borrowed(v_as_2015_, v_i_2016_);
lean_inc(v___x_2020_);
v___x_2021_ = l_Lean_PersistentArray_push___redArg(v_b_2018_, v___x_2020_);
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_2016_, v___x_2022_);
v_i_2016_ = v___x_2023_;
v_b_2018_ = v___x_2021_;
goto _start;
}
else
{
return v_b_2018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg___boxed(lean_object* v_as_2025_, lean_object* v_i_2026_, lean_object* v_stop_2027_, lean_object* v_b_2028_){
_start:
{
size_t v_i_boxed_2029_; size_t v_stop_boxed_2030_; lean_object* v_res_2031_; 
v_i_boxed_2029_ = lean_unbox_usize(v_i_2026_);
lean_dec(v_i_2026_);
v_stop_boxed_2030_ = lean_unbox_usize(v_stop_2027_);
lean_dec(v_stop_2027_);
v_res_2031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2025_, v_i_boxed_2029_, v_stop_boxed_2030_, v_b_2028_);
lean_dec_ref(v_as_2025_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(lean_object* v_x_2032_, lean_object* v_x_2033_){
_start:
{
if (lean_obj_tag(v_x_2032_) == 0)
{
lean_object* v_cs_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; uint8_t v___x_2037_; 
v_cs_2034_ = lean_ctor_get(v_x_2032_, 0);
v___x_2035_ = lean_unsigned_to_nat(0u);
v___x_2036_ = lean_array_get_size(v_cs_2034_);
v___x_2037_ = lean_nat_dec_lt(v___x_2035_, v___x_2036_);
if (v___x_2037_ == 0)
{
return v_x_2033_;
}
else
{
uint8_t v___x_2038_; 
v___x_2038_ = lean_nat_dec_le(v___x_2036_, v___x_2036_);
if (v___x_2038_ == 0)
{
if (v___x_2037_ == 0)
{
return v_x_2033_;
}
else
{
size_t v___x_2039_; size_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = ((size_t)0ULL);
v___x_2040_ = lean_usize_of_nat(v___x_2036_);
v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2034_, v___x_2039_, v___x_2040_, v_x_2033_);
return v___x_2041_;
}
}
else
{
size_t v___x_2042_; size_t v___x_2043_; lean_object* v___x_2044_; 
v___x_2042_ = ((size_t)0ULL);
v___x_2043_ = lean_usize_of_nat(v___x_2036_);
v___x_2044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2034_, v___x_2042_, v___x_2043_, v_x_2033_);
return v___x_2044_;
}
}
}
else
{
lean_object* v_vs_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v_vs_2045_ = lean_ctor_get(v_x_2032_, 0);
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = lean_array_get_size(v_vs_2045_);
v___x_2048_ = lean_nat_dec_lt(v___x_2046_, v___x_2047_);
if (v___x_2048_ == 0)
{
return v_x_2033_;
}
else
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_nat_dec_le(v___x_2047_, v___x_2047_);
if (v___x_2049_ == 0)
{
if (v___x_2048_ == 0)
{
return v_x_2033_;
}
else
{
size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = lean_usize_of_nat(v___x_2047_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2045_, v___x_2050_, v___x_2051_, v_x_2033_);
return v___x_2052_;
}
}
else
{
size_t v___x_2053_; size_t v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = ((size_t)0ULL);
v___x_2054_ = lean_usize_of_nat(v___x_2047_);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2045_, v___x_2053_, v___x_2054_, v_x_2033_);
return v___x_2055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2056_, size_t v_i_2057_, size_t v_stop_2058_, lean_object* v_b_2059_){
_start:
{
uint8_t v___x_2060_; 
v___x_2060_ = lean_usize_dec_eq(v_i_2057_, v_stop_2058_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; lean_object* v___x_2062_; size_t v___x_2063_; size_t v___x_2064_; 
v___x_2061_ = lean_array_uget_borrowed(v_as_2056_, v_i_2057_);
v___x_2062_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v___x_2061_, v_b_2059_);
v___x_2063_ = ((size_t)1ULL);
v___x_2064_ = lean_usize_add(v_i_2057_, v___x_2063_);
v_i_2057_ = v___x_2064_;
v_b_2059_ = v___x_2062_;
goto _start;
}
else
{
return v_b_2059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2066_, lean_object* v_i_2067_, lean_object* v_stop_2068_, lean_object* v_b_2069_){
_start:
{
size_t v_i_boxed_2070_; size_t v_stop_boxed_2071_; lean_object* v_res_2072_; 
v_i_boxed_2070_ = lean_unbox_usize(v_i_2067_);
lean_dec(v_i_2067_);
v_stop_boxed_2071_ = lean_unbox_usize(v_stop_2068_);
lean_dec(v_stop_2068_);
v_res_2072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2066_, v_i_boxed_2070_, v_stop_boxed_2071_, v_b_2069_);
lean_dec_ref(v_as_2066_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(lean_object* v_x_2073_, lean_object* v_x_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2073_, v_x_2074_);
lean_dec_ref(v_x_2073_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(lean_object* v_x_2076_, size_t v_x_2077_, size_t v_x_2078_, lean_object* v_x_2079_){
_start:
{
if (lean_obj_tag(v_x_2076_) == 0)
{
lean_object* v_cs_2080_; lean_object* v___x_2081_; size_t v___x_2082_; lean_object* v_j_2083_; lean_object* v___x_2084_; size_t v___x_2085_; size_t v___x_2086_; size_t v___x_2087_; size_t v___x_2088_; size_t v___x_2089_; size_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v_cs_2080_ = lean_ctor_get(v_x_2076_, 0);
v___x_2081_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_2082_ = lean_usize_shift_right(v_x_2077_, v_x_2078_);
v_j_2083_ = lean_usize_to_nat(v___x_2082_);
v___x_2084_ = lean_array_get_borrowed(v___x_2081_, v_cs_2080_, v_j_2083_);
v___x_2085_ = ((size_t)1ULL);
v___x_2086_ = lean_usize_shift_left(v___x_2085_, v_x_2078_);
v___x_2087_ = lean_usize_sub(v___x_2086_, v___x_2085_);
v___x_2088_ = lean_usize_land(v_x_2077_, v___x_2087_);
v___x_2089_ = ((size_t)5ULL);
v___x_2090_ = lean_usize_sub(v_x_2078_, v___x_2089_);
v___x_2091_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v___x_2084_, v___x_2088_, v___x_2090_, v_x_2079_);
v___x_2092_ = lean_unsigned_to_nat(1u);
v___x_2093_ = lean_nat_add(v_j_2083_, v___x_2092_);
lean_dec(v_j_2083_);
v___x_2094_ = lean_array_get_size(v_cs_2080_);
v___x_2095_ = lean_nat_dec_lt(v___x_2093_, v___x_2094_);
if (v___x_2095_ == 0)
{
lean_dec(v___x_2093_);
return v___x_2091_;
}
else
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_nat_dec_le(v___x_2094_, v___x_2094_);
if (v___x_2096_ == 0)
{
if (v___x_2095_ == 0)
{
lean_dec(v___x_2093_);
return v___x_2091_;
}
else
{
size_t v___x_2097_; size_t v___x_2098_; lean_object* v___x_2099_; 
v___x_2097_ = lean_usize_of_nat(v___x_2093_);
lean_dec(v___x_2093_);
v___x_2098_ = lean_usize_of_nat(v___x_2094_);
v___x_2099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2080_, v___x_2097_, v___x_2098_, v___x_2091_);
return v___x_2099_;
}
}
else
{
size_t v___x_2100_; size_t v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = lean_usize_of_nat(v___x_2093_);
lean_dec(v___x_2093_);
v___x_2101_ = lean_usize_of_nat(v___x_2094_);
v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2080_, v___x_2100_, v___x_2101_, v___x_2091_);
return v___x_2102_;
}
}
}
else
{
lean_object* v_vs_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_vs_2103_ = lean_ctor_get(v_x_2076_, 0);
v___x_2104_ = lean_usize_to_nat(v_x_2077_);
v___x_2105_ = lean_array_get_size(v_vs_2103_);
v___x_2106_ = lean_nat_dec_lt(v___x_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_dec(v___x_2104_);
return v_x_2079_;
}
else
{
uint8_t v___x_2107_; 
v___x_2107_ = lean_nat_dec_le(v___x_2105_, v___x_2105_);
if (v___x_2107_ == 0)
{
if (v___x_2106_ == 0)
{
lean_dec(v___x_2104_);
return v_x_2079_;
}
else
{
size_t v___x_2108_; size_t v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = lean_usize_of_nat(v___x_2104_);
lean_dec(v___x_2104_);
v___x_2109_ = lean_usize_of_nat(v___x_2105_);
v___x_2110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2103_, v___x_2108_, v___x_2109_, v_x_2079_);
return v___x_2110_;
}
}
else
{
size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = lean_usize_of_nat(v___x_2104_);
lean_dec(v___x_2104_);
v___x_2112_ = lean_usize_of_nat(v___x_2105_);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2103_, v___x_2111_, v___x_2112_, v_x_2079_);
return v___x_2113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(lean_object* v_x_2114_, lean_object* v_x_2115_, lean_object* v_x_2116_, lean_object* v_x_2117_){
_start:
{
size_t v_x_1523__boxed_2118_; size_t v_x_1524__boxed_2119_; lean_object* v_res_2120_; 
v_x_1523__boxed_2118_ = lean_unbox_usize(v_x_2115_);
lean_dec(v_x_2115_);
v_x_1524__boxed_2119_ = lean_unbox_usize(v_x_2116_);
lean_dec(v_x_2116_);
v_res_2120_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2114_, v_x_1523__boxed_2118_, v_x_1524__boxed_2119_, v_x_2117_);
lean_dec_ref(v_x_2114_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(lean_object* v_t_2121_, lean_object* v_init_2122_, lean_object* v_start_2123_){
_start:
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = lean_unsigned_to_nat(0u);
v___x_2125_ = lean_nat_dec_eq(v_start_2123_, v___x_2124_);
if (v___x_2125_ == 0)
{
lean_object* v_root_2126_; lean_object* v_tail_2127_; size_t v_shift_2128_; lean_object* v_tailOff_2129_; uint8_t v___x_2130_; 
v_root_2126_ = lean_ctor_get(v_t_2121_, 0);
v_tail_2127_ = lean_ctor_get(v_t_2121_, 1);
v_shift_2128_ = lean_ctor_get_usize(v_t_2121_, 4);
v_tailOff_2129_ = lean_ctor_get(v_t_2121_, 3);
v___x_2130_ = lean_nat_dec_le(v_tailOff_2129_, v_start_2123_);
if (v___x_2130_ == 0)
{
size_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2131_ = lean_usize_of_nat(v_start_2123_);
v___x_2132_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_root_2126_, v___x_2131_, v_shift_2128_, v_init_2122_);
v___x_2133_ = lean_array_get_size(v_tail_2127_);
v___x_2134_ = lean_nat_dec_lt(v___x_2124_, v___x_2133_);
if (v___x_2134_ == 0)
{
return v___x_2132_;
}
else
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_nat_dec_le(v___x_2133_, v___x_2133_);
if (v___x_2135_ == 0)
{
if (v___x_2134_ == 0)
{
return v___x_2132_;
}
else
{
size_t v___x_2136_; size_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2136_ = ((size_t)0ULL);
v___x_2137_ = lean_usize_of_nat(v___x_2133_);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2127_, v___x_2136_, v___x_2137_, v___x_2132_);
return v___x_2138_;
}
}
else
{
size_t v___x_2139_; size_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2139_ = ((size_t)0ULL);
v___x_2140_ = lean_usize_of_nat(v___x_2133_);
v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2127_, v___x_2139_, v___x_2140_, v___x_2132_);
return v___x_2141_;
}
}
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v___x_2142_ = lean_nat_sub(v_start_2123_, v_tailOff_2129_);
v___x_2143_ = lean_array_get_size(v_tail_2127_);
v___x_2144_ = lean_nat_dec_lt(v___x_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_dec(v___x_2142_);
return v_init_2122_;
}
else
{
uint8_t v___x_2145_; 
v___x_2145_ = lean_nat_dec_le(v___x_2143_, v___x_2143_);
if (v___x_2145_ == 0)
{
if (v___x_2144_ == 0)
{
lean_dec(v___x_2142_);
return v_init_2122_;
}
else
{
size_t v___x_2146_; size_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = lean_usize_of_nat(v___x_2142_);
lean_dec(v___x_2142_);
v___x_2147_ = lean_usize_of_nat(v___x_2143_);
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2127_, v___x_2146_, v___x_2147_, v_init_2122_);
return v___x_2148_;
}
}
else
{
size_t v___x_2149_; size_t v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = lean_usize_of_nat(v___x_2142_);
lean_dec(v___x_2142_);
v___x_2150_ = lean_usize_of_nat(v___x_2143_);
v___x_2151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2127_, v___x_2149_, v___x_2150_, v_init_2122_);
return v___x_2151_;
}
}
}
}
else
{
lean_object* v_root_2152_; lean_object* v_tail_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v_root_2152_ = lean_ctor_get(v_t_2121_, 0);
v_tail_2153_ = lean_ctor_get(v_t_2121_, 1);
v___x_2154_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_root_2152_, v_init_2122_);
v___x_2155_ = lean_array_get_size(v_tail_2153_);
v___x_2156_ = lean_nat_dec_lt(v___x_2124_, v___x_2155_);
if (v___x_2156_ == 0)
{
return v___x_2154_;
}
else
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_nat_dec_le(v___x_2155_, v___x_2155_);
if (v___x_2157_ == 0)
{
if (v___x_2156_ == 0)
{
return v___x_2154_;
}
else
{
size_t v___x_2158_; size_t v___x_2159_; lean_object* v___x_2160_; 
v___x_2158_ = ((size_t)0ULL);
v___x_2159_ = lean_usize_of_nat(v___x_2155_);
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2153_, v___x_2158_, v___x_2159_, v___x_2154_);
return v___x_2160_;
}
}
else
{
size_t v___x_2161_; size_t v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = ((size_t)0ULL);
v___x_2162_ = lean_usize_of_nat(v___x_2155_);
v___x_2163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2153_, v___x_2161_, v___x_2162_, v___x_2154_);
return v___x_2163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(lean_object* v_t_2164_, lean_object* v_init_2165_, lean_object* v_start_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2164_, v_init_2165_, v_start_2166_);
lean_dec(v_start_2166_);
lean_dec_ref(v_t_2164_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg(lean_object* v_t_u2081_2168_, lean_object* v_t_u2082_2169_){
_start:
{
uint8_t v___x_2170_; 
v___x_2170_ = l_Lean_PersistentArray_isEmpty___redArg(v_t_u2081_2168_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_u2082_2169_, v_t_u2081_2168_, v___x_2171_);
return v___x_2172_;
}
else
{
lean_dec_ref(v_t_u2081_2168_);
lean_inc_ref(v_t_u2082_2169_);
return v_t_u2082_2169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg___boxed(lean_object* v_t_u2081_2173_, lean_object* v_t_u2082_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2173_, v_t_u2082_2174_);
lean_dec_ref(v_t_u2082_2174_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append(lean_object* v_00_u03b1_2176_, lean_object* v_t_u2081_2177_, lean_object* v_t_u2082_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2177_, v_t_u2082_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___boxed(lean_object* v_00_u03b1_2180_, lean_object* v_t_u2081_2181_, lean_object* v_t_u2082_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_PersistentArray_append(v_00_u03b1_2180_, v_t_u2081_2181_, v_t_u2082_2182_);
lean_dec_ref(v_t_u2082_2182_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(lean_object* v_00_u03b1_2184_, lean_object* v_t_2185_, lean_object* v_init_2186_, lean_object* v_start_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2185_, v_init_2186_, v_start_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(lean_object* v_00_u03b1_2189_, lean_object* v_t_2190_, lean_object* v_init_2191_, lean_object* v_start_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(v_00_u03b1_2189_, v_t_2190_, v_init_2191_, v_start_2192_);
lean_dec(v_start_2192_);
lean_dec_ref(v_t_2190_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(lean_object* v_00_u03b1_2194_, lean_object* v_x_2195_, size_t v_x_2196_, size_t v_x_2197_, lean_object* v_x_2198_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2195_, v_x_2196_, v_x_2197_, v_x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
size_t v_x_1679__boxed_2205_; size_t v_x_1680__boxed_2206_; lean_object* v_res_2207_; 
v_x_1679__boxed_2205_ = lean_unbox_usize(v_x_2202_);
lean_dec(v_x_2202_);
v_x_1680__boxed_2206_ = lean_unbox_usize(v_x_2203_);
lean_dec(v_x_2203_);
v_res_2207_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(v_00_u03b1_2200_, v_x_2201_, v_x_1679__boxed_2205_, v_x_1680__boxed_2206_, v_x_2204_);
lean_dec_ref(v_x_2201_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(lean_object* v_00_u03b1_2208_, lean_object* v_as_2209_, size_t v_i_2210_, size_t v_stop_2211_, lean_object* v_b_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2209_, v_i_2210_, v_stop_2211_, v_b_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2214_, lean_object* v_as_2215_, lean_object* v_i_2216_, lean_object* v_stop_2217_, lean_object* v_b_2218_){
_start:
{
size_t v_i_boxed_2219_; size_t v_stop_boxed_2220_; lean_object* v_res_2221_; 
v_i_boxed_2219_ = lean_unbox_usize(v_i_2216_);
lean_dec(v_i_2216_);
v_stop_boxed_2220_ = lean_unbox_usize(v_stop_2217_);
lean_dec(v_stop_2217_);
v_res_2221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(v_00_u03b1_2214_, v_as_2215_, v_i_boxed_2219_, v_stop_boxed_2220_, v_b_2218_);
lean_dec_ref(v_as_2215_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(lean_object* v_00_u03b1_2222_, lean_object* v_x_2223_, lean_object* v_x_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2223_, v_x_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2226_, lean_object* v_x_2227_, lean_object* v_x_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(v_00_u03b1_2226_, v_x_2227_, v_x_2228_);
lean_dec_ref(v_x_2227_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2230_, lean_object* v_as_2231_, size_t v_i_2232_, size_t v_stop_2233_, lean_object* v_b_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2231_, v_i_2232_, v_stop_2233_, v_b_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2236_, lean_object* v_as_2237_, lean_object* v_i_2238_, lean_object* v_stop_2239_, lean_object* v_b_2240_){
_start:
{
size_t v_i_boxed_2241_; size_t v_stop_boxed_2242_; lean_object* v_res_2243_; 
v_i_boxed_2241_ = lean_unbox_usize(v_i_2238_);
lean_dec(v_i_2238_);
v_stop_boxed_2242_ = lean_unbox_usize(v_stop_2239_);
lean_dec(v_stop_2239_);
v_res_2243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(v_00_u03b1_2236_, v_as_2237_, v_i_boxed_2241_, v_stop_boxed_2242_, v_b_2240_);
lean_dec_ref(v_as_2237_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend(lean_object* v_00_u03b1_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___closed__0));
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(lean_object* v_f_2247_, lean_object* v_x_2248_){
_start:
{
lean_object* v___x_2249_; 
v___x_2249_ = lean_apply_1(v_f_2247_, v_x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg(lean_object* v_t_2250_, lean_object* v_f_2251_){
_start:
{
lean_object* v___f_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___f_2252_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2252_, 0, v_f_2251_);
v___x_2253_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2254_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2253_, v_t_2250_, v___f_2252_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f(lean_object* v_00_u03b1_2255_, lean_object* v_00_u03b2_2256_, lean_object* v_t_2257_, lean_object* v_f_2258_){
_start:
{
lean_object* v___f_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___f_2259_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2259_, 0, v_f_2258_);
v___x_2260_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2261_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2260_, v_t_2257_, v___f_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f___redArg(lean_object* v_t_2262_, lean_object* v_f_2263_){
_start:
{
lean_object* v___f_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___f_2264_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2264_, 0, v_f_2263_);
v___x_2265_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2266_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2265_, v_t_2262_, v___f_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f(lean_object* v_00_u03b1_2267_, lean_object* v_00_u03b2_2268_, lean_object* v_t_2269_, lean_object* v_f_2270_){
_start:
{
lean_object* v___f_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___f_2271_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2271_, 0, v_f_2270_);
v___x_2272_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2273_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2272_, v_t_2269_, v___f_2271_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(lean_object* v_as_2274_, size_t v_i_2275_, size_t v_stop_2276_, lean_object* v_b_2277_){
_start:
{
uint8_t v___x_2278_; 
v___x_2278_ = lean_usize_dec_eq(v_i_2275_, v_stop_2276_);
if (v___x_2278_ == 0)
{
lean_object* v___x_2279_; lean_object* v___x_2280_; size_t v___x_2281_; size_t v___x_2282_; 
v___x_2279_ = lean_array_uget_borrowed(v_as_2274_, v_i_2275_);
lean_inc(v___x_2279_);
v___x_2280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v_b_2277_);
v___x_2281_ = ((size_t)1ULL);
v___x_2282_ = lean_usize_add(v_i_2275_, v___x_2281_);
v_i_2275_ = v___x_2282_;
v_b_2277_ = v___x_2280_;
goto _start;
}
else
{
return v_b_2277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg___boxed(lean_object* v_as_2284_, lean_object* v_i_2285_, lean_object* v_stop_2286_, lean_object* v_b_2287_){
_start:
{
size_t v_i_boxed_2288_; size_t v_stop_boxed_2289_; lean_object* v_res_2290_; 
v_i_boxed_2288_ = lean_unbox_usize(v_i_2285_);
lean_dec(v_i_2285_);
v_stop_boxed_2289_ = lean_unbox_usize(v_stop_2286_);
lean_dec(v_stop_2286_);
v_res_2290_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2284_, v_i_boxed_2288_, v_stop_boxed_2289_, v_b_2287_);
lean_dec_ref(v_as_2284_);
return v_res_2290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(lean_object* v_x_2291_, lean_object* v_x_2292_){
_start:
{
if (lean_obj_tag(v_x_2291_) == 0)
{
lean_object* v_cs_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v_cs_2293_ = lean_ctor_get(v_x_2291_, 0);
v___x_2294_ = lean_unsigned_to_nat(0u);
v___x_2295_ = lean_array_get_size(v_cs_2293_);
v___x_2296_ = lean_nat_dec_lt(v___x_2294_, v___x_2295_);
if (v___x_2296_ == 0)
{
return v_x_2292_;
}
else
{
uint8_t v___x_2297_; 
v___x_2297_ = lean_nat_dec_le(v___x_2295_, v___x_2295_);
if (v___x_2297_ == 0)
{
if (v___x_2296_ == 0)
{
return v_x_2292_;
}
else
{
size_t v___x_2298_; size_t v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = ((size_t)0ULL);
v___x_2299_ = lean_usize_of_nat(v___x_2295_);
v___x_2300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2293_, v___x_2298_, v___x_2299_, v_x_2292_);
return v___x_2300_;
}
}
else
{
size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = ((size_t)0ULL);
v___x_2302_ = lean_usize_of_nat(v___x_2295_);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2293_, v___x_2301_, v___x_2302_, v_x_2292_);
return v___x_2303_;
}
}
}
else
{
lean_object* v_vs_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; uint8_t v___x_2307_; 
v_vs_2304_ = lean_ctor_get(v_x_2291_, 0);
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = lean_array_get_size(v_vs_2304_);
v___x_2307_ = lean_nat_dec_lt(v___x_2305_, v___x_2306_);
if (v___x_2307_ == 0)
{
return v_x_2292_;
}
else
{
uint8_t v___x_2308_; 
v___x_2308_ = lean_nat_dec_le(v___x_2306_, v___x_2306_);
if (v___x_2308_ == 0)
{
if (v___x_2307_ == 0)
{
return v_x_2292_;
}
else
{
size_t v___x_2309_; size_t v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = ((size_t)0ULL);
v___x_2310_ = lean_usize_of_nat(v___x_2306_);
v___x_2311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2304_, v___x_2309_, v___x_2310_, v_x_2292_);
return v___x_2311_;
}
}
else
{
size_t v___x_2312_; size_t v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = ((size_t)0ULL);
v___x_2313_ = lean_usize_of_nat(v___x_2306_);
v___x_2314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2304_, v___x_2312_, v___x_2313_, v_x_2292_);
return v___x_2314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2315_, size_t v_i_2316_, size_t v_stop_2317_, lean_object* v_b_2318_){
_start:
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_usize_dec_eq(v_i_2316_, v_stop_2317_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v___x_2321_; size_t v___x_2322_; size_t v___x_2323_; 
v___x_2320_ = lean_array_uget_borrowed(v_as_2315_, v_i_2316_);
v___x_2321_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v___x_2320_, v_b_2318_);
v___x_2322_ = ((size_t)1ULL);
v___x_2323_ = lean_usize_add(v_i_2316_, v___x_2322_);
v_i_2316_ = v___x_2323_;
v_b_2318_ = v___x_2321_;
goto _start;
}
else
{
return v_b_2318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2325_, lean_object* v_i_2326_, lean_object* v_stop_2327_, lean_object* v_b_2328_){
_start:
{
size_t v_i_boxed_2329_; size_t v_stop_boxed_2330_; lean_object* v_res_2331_; 
v_i_boxed_2329_ = lean_unbox_usize(v_i_2326_);
lean_dec(v_i_2326_);
v_stop_boxed_2330_ = lean_unbox_usize(v_stop_2327_);
lean_dec(v_stop_2327_);
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2325_, v_i_boxed_2329_, v_stop_boxed_2330_, v_b_2328_);
lean_dec_ref(v_as_2325_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(lean_object* v_x_2332_, lean_object* v_x_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2332_, v_x_2333_);
lean_dec_ref(v_x_2332_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(lean_object* v_x_2335_, size_t v_x_2336_, size_t v_x_2337_, lean_object* v_x_2338_){
_start:
{
if (lean_obj_tag(v_x_2335_) == 0)
{
lean_object* v_cs_2339_; lean_object* v___x_2340_; size_t v___x_2341_; lean_object* v_j_2342_; lean_object* v___x_2343_; size_t v___x_2344_; size_t v___x_2345_; size_t v___x_2346_; size_t v___x_2347_; size_t v___x_2348_; size_t v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v_cs_2339_ = lean_ctor_get(v_x_2335_, 0);
v___x_2340_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_2341_ = lean_usize_shift_right(v_x_2336_, v_x_2337_);
v_j_2342_ = lean_usize_to_nat(v___x_2341_);
v___x_2343_ = lean_array_get_borrowed(v___x_2340_, v_cs_2339_, v_j_2342_);
v___x_2344_ = ((size_t)1ULL);
v___x_2345_ = lean_usize_shift_left(v___x_2344_, v_x_2337_);
v___x_2346_ = lean_usize_sub(v___x_2345_, v___x_2344_);
v___x_2347_ = lean_usize_land(v_x_2336_, v___x_2346_);
v___x_2348_ = ((size_t)5ULL);
v___x_2349_ = lean_usize_sub(v_x_2337_, v___x_2348_);
v___x_2350_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v___x_2343_, v___x_2347_, v___x_2349_, v_x_2338_);
v___x_2351_ = lean_unsigned_to_nat(1u);
v___x_2352_ = lean_nat_add(v_j_2342_, v___x_2351_);
lean_dec(v_j_2342_);
v___x_2353_ = lean_array_get_size(v_cs_2339_);
v___x_2354_ = lean_nat_dec_lt(v___x_2352_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_dec(v___x_2352_);
return v___x_2350_;
}
else
{
uint8_t v___x_2355_; 
v___x_2355_ = lean_nat_dec_le(v___x_2353_, v___x_2353_);
if (v___x_2355_ == 0)
{
if (v___x_2354_ == 0)
{
lean_dec(v___x_2352_);
return v___x_2350_;
}
else
{
size_t v___x_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = lean_usize_of_nat(v___x_2352_);
lean_dec(v___x_2352_);
v___x_2357_ = lean_usize_of_nat(v___x_2353_);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2339_, v___x_2356_, v___x_2357_, v___x_2350_);
return v___x_2358_;
}
}
else
{
size_t v___x_2359_; size_t v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = lean_usize_of_nat(v___x_2352_);
lean_dec(v___x_2352_);
v___x_2360_ = lean_usize_of_nat(v___x_2353_);
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2339_, v___x_2359_, v___x_2360_, v___x_2350_);
return v___x_2361_;
}
}
}
else
{
lean_object* v_vs_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; 
v_vs_2362_ = lean_ctor_get(v_x_2335_, 0);
v___x_2363_ = lean_usize_to_nat(v_x_2336_);
v___x_2364_ = lean_array_get_size(v_vs_2362_);
v___x_2365_ = lean_nat_dec_lt(v___x_2363_, v___x_2364_);
if (v___x_2365_ == 0)
{
lean_dec(v___x_2363_);
return v_x_2338_;
}
else
{
uint8_t v___x_2366_; 
v___x_2366_ = lean_nat_dec_le(v___x_2364_, v___x_2364_);
if (v___x_2366_ == 0)
{
if (v___x_2365_ == 0)
{
lean_dec(v___x_2363_);
return v_x_2338_;
}
else
{
size_t v___x_2367_; size_t v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = lean_usize_of_nat(v___x_2363_);
lean_dec(v___x_2363_);
v___x_2368_ = lean_usize_of_nat(v___x_2364_);
v___x_2369_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2362_, v___x_2367_, v___x_2368_, v_x_2338_);
return v___x_2369_;
}
}
else
{
size_t v___x_2370_; size_t v___x_2371_; lean_object* v___x_2372_; 
v___x_2370_ = lean_usize_of_nat(v___x_2363_);
lean_dec(v___x_2363_);
v___x_2371_ = lean_usize_of_nat(v___x_2364_);
v___x_2372_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2362_, v___x_2370_, v___x_2371_, v_x_2338_);
return v___x_2372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(lean_object* v_x_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
size_t v_x_1497__boxed_2377_; size_t v_x_1498__boxed_2378_; lean_object* v_res_2379_; 
v_x_1497__boxed_2377_ = lean_unbox_usize(v_x_2374_);
lean_dec(v_x_2374_);
v_x_1498__boxed_2378_ = lean_unbox_usize(v_x_2375_);
lean_dec(v_x_2375_);
v_res_2379_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2373_, v_x_1497__boxed_2377_, v_x_1498__boxed_2378_, v_x_2376_);
lean_dec_ref(v_x_2373_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(lean_object* v_t_2380_, lean_object* v_init_2381_, lean_object* v_start_2382_){
_start:
{
lean_object* v___x_2383_; uint8_t v___x_2384_; 
v___x_2383_ = lean_unsigned_to_nat(0u);
v___x_2384_ = lean_nat_dec_eq(v_start_2382_, v___x_2383_);
if (v___x_2384_ == 0)
{
lean_object* v_root_2385_; lean_object* v_tail_2386_; size_t v_shift_2387_; lean_object* v_tailOff_2388_; uint8_t v___x_2389_; 
v_root_2385_ = lean_ctor_get(v_t_2380_, 0);
v_tail_2386_ = lean_ctor_get(v_t_2380_, 1);
v_shift_2387_ = lean_ctor_get_usize(v_t_2380_, 4);
v_tailOff_2388_ = lean_ctor_get(v_t_2380_, 3);
v___x_2389_ = lean_nat_dec_le(v_tailOff_2388_, v_start_2382_);
if (v___x_2389_ == 0)
{
size_t v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v___x_2390_ = lean_usize_of_nat(v_start_2382_);
v___x_2391_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_root_2385_, v___x_2390_, v_shift_2387_, v_init_2381_);
v___x_2392_ = lean_array_get_size(v_tail_2386_);
v___x_2393_ = lean_nat_dec_lt(v___x_2383_, v___x_2392_);
if (v___x_2393_ == 0)
{
return v___x_2391_;
}
else
{
uint8_t v___x_2394_; 
v___x_2394_ = lean_nat_dec_le(v___x_2392_, v___x_2392_);
if (v___x_2394_ == 0)
{
if (v___x_2393_ == 0)
{
return v___x_2391_;
}
else
{
size_t v___x_2395_; size_t v___x_2396_; lean_object* v___x_2397_; 
v___x_2395_ = ((size_t)0ULL);
v___x_2396_ = lean_usize_of_nat(v___x_2392_);
v___x_2397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2386_, v___x_2395_, v___x_2396_, v___x_2391_);
return v___x_2397_;
}
}
else
{
size_t v___x_2398_; size_t v___x_2399_; lean_object* v___x_2400_; 
v___x_2398_ = ((size_t)0ULL);
v___x_2399_ = lean_usize_of_nat(v___x_2392_);
v___x_2400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2386_, v___x_2398_, v___x_2399_, v___x_2391_);
return v___x_2400_;
}
}
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v___x_2401_ = lean_nat_sub(v_start_2382_, v_tailOff_2388_);
v___x_2402_ = lean_array_get_size(v_tail_2386_);
v___x_2403_ = lean_nat_dec_lt(v___x_2401_, v___x_2402_);
if (v___x_2403_ == 0)
{
lean_dec(v___x_2401_);
return v_init_2381_;
}
else
{
uint8_t v___x_2404_; 
v___x_2404_ = lean_nat_dec_le(v___x_2402_, v___x_2402_);
if (v___x_2404_ == 0)
{
if (v___x_2403_ == 0)
{
lean_dec(v___x_2401_);
return v_init_2381_;
}
else
{
size_t v___x_2405_; size_t v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = lean_usize_of_nat(v___x_2401_);
lean_dec(v___x_2401_);
v___x_2406_ = lean_usize_of_nat(v___x_2402_);
v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2386_, v___x_2405_, v___x_2406_, v_init_2381_);
return v___x_2407_;
}
}
else
{
size_t v___x_2408_; size_t v___x_2409_; lean_object* v___x_2410_; 
v___x_2408_ = lean_usize_of_nat(v___x_2401_);
lean_dec(v___x_2401_);
v___x_2409_ = lean_usize_of_nat(v___x_2402_);
v___x_2410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2386_, v___x_2408_, v___x_2409_, v_init_2381_);
return v___x_2410_;
}
}
}
}
else
{
lean_object* v_root_2411_; lean_object* v_tail_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v_root_2411_ = lean_ctor_get(v_t_2380_, 0);
v_tail_2412_ = lean_ctor_get(v_t_2380_, 1);
v___x_2413_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_root_2411_, v_init_2381_);
v___x_2414_ = lean_array_get_size(v_tail_2412_);
v___x_2415_ = lean_nat_dec_lt(v___x_2383_, v___x_2414_);
if (v___x_2415_ == 0)
{
return v___x_2413_;
}
else
{
uint8_t v___x_2416_; 
v___x_2416_ = lean_nat_dec_le(v___x_2414_, v___x_2414_);
if (v___x_2416_ == 0)
{
if (v___x_2415_ == 0)
{
return v___x_2413_;
}
else
{
size_t v___x_2417_; size_t v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = ((size_t)0ULL);
v___x_2418_ = lean_usize_of_nat(v___x_2414_);
v___x_2419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2412_, v___x_2417_, v___x_2418_, v___x_2413_);
return v___x_2419_;
}
}
else
{
size_t v___x_2420_; size_t v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = ((size_t)0ULL);
v___x_2421_ = lean_usize_of_nat(v___x_2414_);
v___x_2422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2412_, v___x_2420_, v___x_2421_, v___x_2413_);
return v___x_2422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(lean_object* v_t_2423_, lean_object* v_init_2424_, lean_object* v_start_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2423_, v_init_2424_, v_start_2425_);
lean_dec(v_start_2425_);
lean_dec_ref(v_t_2423_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg(lean_object* v_t_2427_){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2428_ = lean_box(0);
v___x_2429_ = lean_unsigned_to_nat(0u);
v___x_2430_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2427_, v___x_2428_, v___x_2429_);
v___x_2431_ = l_List_reverse___redArg(v___x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg___boxed(lean_object* v_t_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_PersistentArray_toList___redArg(v_t_2432_);
lean_dec_ref(v_t_2432_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList(lean_object* v_00_u03b1_2434_, lean_object* v_t_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_PersistentArray_toList___redArg(v_t_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___boxed(lean_object* v_00_u03b1_2437_, lean_object* v_t_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_PersistentArray_toList(v_00_u03b1_2437_, v_t_2438_);
lean_dec_ref(v_t_2438_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(lean_object* v_00_u03b1_2440_, lean_object* v_t_2441_, lean_object* v_init_2442_, lean_object* v_start_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2441_, v_init_2442_, v_start_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(lean_object* v_00_u03b1_2445_, lean_object* v_t_2446_, lean_object* v_init_2447_, lean_object* v_start_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(v_00_u03b1_2445_, v_t_2446_, v_init_2447_, v_start_2448_);
lean_dec(v_start_2448_);
lean_dec_ref(v_t_2446_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(lean_object* v_00_u03b1_2450_, lean_object* v_x_2451_, size_t v_x_2452_, size_t v_x_2453_, lean_object* v_x_2454_){
_start:
{
lean_object* v___x_2455_; 
v___x_2455_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2451_, v_x_2452_, v_x_2453_, v_x_2454_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2456_, lean_object* v_x_2457_, lean_object* v_x_2458_, lean_object* v_x_2459_, lean_object* v_x_2460_){
_start:
{
size_t v_x_1655__boxed_2461_; size_t v_x_1656__boxed_2462_; lean_object* v_res_2463_; 
v_x_1655__boxed_2461_ = lean_unbox_usize(v_x_2458_);
lean_dec(v_x_2458_);
v_x_1656__boxed_2462_ = lean_unbox_usize(v_x_2459_);
lean_dec(v_x_2459_);
v_res_2463_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(v_00_u03b1_2456_, v_x_2457_, v_x_1655__boxed_2461_, v_x_1656__boxed_2462_, v_x_2460_);
lean_dec_ref(v_x_2457_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(lean_object* v_00_u03b1_2464_, lean_object* v_as_2465_, size_t v_i_2466_, size_t v_stop_2467_, lean_object* v_b_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2465_, v_i_2466_, v_stop_2467_, v_b_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2470_, lean_object* v_as_2471_, lean_object* v_i_2472_, lean_object* v_stop_2473_, lean_object* v_b_2474_){
_start:
{
size_t v_i_boxed_2475_; size_t v_stop_boxed_2476_; lean_object* v_res_2477_; 
v_i_boxed_2475_ = lean_unbox_usize(v_i_2472_);
lean_dec(v_i_2472_);
v_stop_boxed_2476_ = lean_unbox_usize(v_stop_2473_);
lean_dec(v_stop_2473_);
v_res_2477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(v_00_u03b1_2470_, v_as_2471_, v_i_boxed_2475_, v_stop_boxed_2476_, v_b_2474_);
lean_dec_ref(v_as_2471_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(lean_object* v_00_u03b1_2478_, lean_object* v_x_2479_, lean_object* v_x_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2479_, v_x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2482_, lean_object* v_x_2483_, lean_object* v_x_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(v_00_u03b1_2482_, v_x_2483_, v_x_2484_);
lean_dec_ref(v_x_2483_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2486_, lean_object* v_as_2487_, size_t v_i_2488_, size_t v_stop_2489_, lean_object* v_b_2490_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2487_, v_i_2488_, v_stop_2489_, v_b_2490_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2492_, lean_object* v_as_2493_, lean_object* v_i_2494_, lean_object* v_stop_2495_, lean_object* v_b_2496_){
_start:
{
size_t v_i_boxed_2497_; size_t v_stop_boxed_2498_; lean_object* v_res_2499_; 
v_i_boxed_2497_ = lean_unbox_usize(v_i_2494_);
lean_dec(v_i_2494_);
v_stop_boxed_2498_ = lean_unbox_usize(v_stop_2495_);
lean_dec(v_stop_2495_);
v_res_2499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(v_00_u03b1_2492_, v_as_2493_, v_i_boxed_2497_, v_stop_boxed_2498_, v_b_2496_);
lean_dec_ref(v_as_2493_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg(lean_object* v_inst_2500_, lean_object* v_p_2501_, lean_object* v_x_2502_){
_start:
{
if (lean_obj_tag(v_x_2502_) == 0)
{
lean_object* v_cs_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_cs_2503_ = lean_ctor_get(v_x_2502_, 0);
lean_inc_ref(v_cs_2503_);
lean_dec_ref(v_x_2502_);
v___x_2504_ = lean_unsigned_to_nat(0u);
v___x_2505_ = lean_array_get_size(v_cs_2503_);
v___x_2506_ = lean_nat_dec_lt(v___x_2504_, v___x_2505_);
if (v___x_2506_ == 0)
{
lean_object* v_toApplicative_2507_; lean_object* v_toPure_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec_ref(v_cs_2503_);
lean_dec(v_p_2501_);
v_toApplicative_2507_ = lean_ctor_get(v_inst_2500_, 0);
lean_inc_ref(v_toApplicative_2507_);
lean_dec_ref(v_inst_2500_);
v_toPure_2508_ = lean_ctor_get(v_toApplicative_2507_, 1);
lean_inc(v_toPure_2508_);
lean_dec_ref(v_toApplicative_2507_);
v___x_2509_ = lean_box(v___x_2506_);
v___x_2510_ = lean_apply_2(v_toPure_2508_, lean_box(0), v___x_2509_);
return v___x_2510_;
}
else
{
if (v___x_2506_ == 0)
{
lean_object* v_toApplicative_2511_; lean_object* v_toPure_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_dec_ref(v_cs_2503_);
lean_dec(v_p_2501_);
v_toApplicative_2511_ = lean_ctor_get(v_inst_2500_, 0);
lean_inc_ref(v_toApplicative_2511_);
lean_dec_ref(v_inst_2500_);
v_toPure_2512_ = lean_ctor_get(v_toApplicative_2511_, 1);
lean_inc(v_toPure_2512_);
lean_dec_ref(v_toApplicative_2511_);
v___x_2513_ = lean_box(v___x_2506_);
v___x_2514_ = lean_apply_2(v_toPure_2512_, lean_box(0), v___x_2513_);
return v___x_2514_;
}
else
{
lean_object* v___f_2515_; size_t v___x_2516_; size_t v___x_2517_; lean_object* v___x_2518_; 
lean_inc_ref(v_inst_2500_);
v___f_2515_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2515_, 0, v_inst_2500_);
lean_closure_set(v___f_2515_, 1, v_p_2501_);
v___x_2516_ = ((size_t)0ULL);
v___x_2517_ = lean_usize_of_nat(v___x_2505_);
v___x_2518_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2500_, v___f_2515_, v_cs_2503_, v___x_2516_, v___x_2517_);
return v___x_2518_;
}
}
}
else
{
lean_object* v_vs_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v_vs_2519_ = lean_ctor_get(v_x_2502_, 0);
lean_inc_ref(v_vs_2519_);
lean_dec_ref(v_x_2502_);
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = lean_array_get_size(v_vs_2519_);
v___x_2522_ = lean_nat_dec_lt(v___x_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_object* v_toApplicative_2523_; lean_object* v_toPure_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec_ref(v_vs_2519_);
lean_dec(v_p_2501_);
v_toApplicative_2523_ = lean_ctor_get(v_inst_2500_, 0);
lean_inc_ref(v_toApplicative_2523_);
lean_dec_ref(v_inst_2500_);
v_toPure_2524_ = lean_ctor_get(v_toApplicative_2523_, 1);
lean_inc(v_toPure_2524_);
lean_dec_ref(v_toApplicative_2523_);
v___x_2525_ = lean_box(v___x_2522_);
v___x_2526_ = lean_apply_2(v_toPure_2524_, lean_box(0), v___x_2525_);
return v___x_2526_;
}
else
{
if (v___x_2522_ == 0)
{
lean_object* v_toApplicative_2527_; lean_object* v_toPure_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec_ref(v_vs_2519_);
lean_dec(v_p_2501_);
v_toApplicative_2527_ = lean_ctor_get(v_inst_2500_, 0);
lean_inc_ref(v_toApplicative_2527_);
lean_dec_ref(v_inst_2500_);
v_toPure_2528_ = lean_ctor_get(v_toApplicative_2527_, 1);
lean_inc(v_toPure_2528_);
lean_dec_ref(v_toApplicative_2527_);
v___x_2529_ = lean_box(v___x_2522_);
v___x_2530_ = lean_apply_2(v_toPure_2528_, lean_box(0), v___x_2529_);
return v___x_2530_;
}
else
{
size_t v___x_2531_; size_t v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = ((size_t)0ULL);
v___x_2532_ = lean_usize_of_nat(v___x_2521_);
v___x_2533_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2500_, v_p_2501_, v_vs_2519_, v___x_2531_, v___x_2532_);
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg___lam__0(lean_object* v_inst_2534_, lean_object* v_p_2535_, lean_object* v_c_2536_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2534_, v_p_2535_, v_c_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux(lean_object* v_00_u03b1_2538_, lean_object* v_m_2539_, lean_object* v_inst_2540_, lean_object* v_p_2541_, lean_object* v_x_2542_){
_start:
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2540_, v_p_2541_, v_x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0(lean_object* v_tail_2544_, lean_object* v_toPure_2545_, lean_object* v_inst_2546_, lean_object* v_p_2547_, uint8_t v_b_2548_){
_start:
{
if (v_b_2548_ == 0)
{
lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = lean_array_get_size(v_tail_2544_);
v___x_2551_ = lean_nat_dec_lt(v___x_2549_, v___x_2550_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
lean_dec(v_p_2547_);
lean_dec_ref(v_inst_2546_);
lean_dec_ref(v_tail_2544_);
v___x_2552_ = lean_box(v_b_2548_);
v___x_2553_ = lean_apply_2(v_toPure_2545_, lean_box(0), v___x_2552_);
return v___x_2553_;
}
else
{
if (v___x_2551_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_dec(v_p_2547_);
lean_dec_ref(v_inst_2546_);
lean_dec_ref(v_tail_2544_);
v___x_2554_ = lean_box(v_b_2548_);
v___x_2555_ = lean_apply_2(v_toPure_2545_, lean_box(0), v___x_2554_);
return v___x_2555_;
}
else
{
size_t v___x_2556_; size_t v___x_2557_; lean_object* v___x_2558_; 
lean_dec(v_toPure_2545_);
v___x_2556_ = ((size_t)0ULL);
v___x_2557_ = lean_usize_of_nat(v___x_2550_);
v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2546_, v_p_2547_, v_tail_2544_, v___x_2556_, v___x_2557_);
return v___x_2558_;
}
}
}
else
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_dec(v_p_2547_);
lean_dec_ref(v_inst_2546_);
lean_dec_ref(v_tail_2544_);
v___x_2559_ = lean_box(v_b_2548_);
v___x_2560_ = lean_apply_2(v_toPure_2545_, lean_box(0), v___x_2559_);
return v___x_2560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(lean_object* v_tail_2561_, lean_object* v_toPure_2562_, lean_object* v_inst_2563_, lean_object* v_p_2564_, lean_object* v_b_2565_){
_start:
{
uint8_t v_b_boxed_2566_; lean_object* v_res_2567_; 
v_b_boxed_2566_ = lean_unbox(v_b_2565_);
v_res_2567_ = l_Lean_PersistentArray_anyM___redArg___lam__0(v_tail_2561_, v_toPure_2562_, v_inst_2563_, v_p_2564_, v_b_boxed_2566_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object* v_inst_2568_, lean_object* v_t_2569_, lean_object* v_p_2570_){
_start:
{
lean_object* v_toApplicative_2571_; lean_object* v_toBind_2572_; lean_object* v_root_2573_; lean_object* v_tail_2574_; lean_object* v_toPure_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; lean_object* v___x_2578_; 
v_toApplicative_2571_ = lean_ctor_get(v_inst_2568_, 0);
v_toBind_2572_ = lean_ctor_get(v_inst_2568_, 1);
lean_inc(v_toBind_2572_);
v_root_2573_ = lean_ctor_get(v_t_2569_, 0);
lean_inc_ref(v_root_2573_);
v_tail_2574_ = lean_ctor_get(v_t_2569_, 1);
lean_inc_ref(v_tail_2574_);
lean_dec_ref(v_t_2569_);
v_toPure_2575_ = lean_ctor_get(v_toApplicative_2571_, 1);
lean_inc(v_toPure_2575_);
lean_inc(v_p_2570_);
lean_inc_ref(v_inst_2568_);
v___x_2576_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2568_, v_p_2570_, v_root_2573_);
v___f_2577_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2577_, 0, v_tail_2574_);
lean_closure_set(v___f_2577_, 1, v_toPure_2575_);
lean_closure_set(v___f_2577_, 2, v_inst_2568_);
lean_closure_set(v___f_2577_, 3, v_p_2570_);
v___x_2578_ = lean_apply_4(v_toBind_2572_, lean_box(0), lean_box(0), v___x_2576_, v___f_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM(lean_object* v_00_u03b1_2579_, lean_object* v_m_2580_, lean_object* v_inst_2581_, lean_object* v_t_2582_, lean_object* v_p_2583_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2581_, v_t_2582_, v_p_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0(lean_object* v_toPure_2585_, uint8_t v_b_2586_){
_start:
{
if (v_b_2586_ == 0)
{
uint8_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = 1;
v___x_2588_ = lean_box(v___x_2587_);
v___x_2589_ = lean_apply_2(v_toPure_2585_, lean_box(0), v___x_2588_);
return v___x_2589_;
}
else
{
uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = 0;
v___x_2591_ = lean_box(v___x_2590_);
v___x_2592_ = lean_apply_2(v_toPure_2585_, lean_box(0), v___x_2591_);
return v___x_2592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0___boxed(lean_object* v_toPure_2593_, lean_object* v_b_2594_){
_start:
{
uint8_t v_b_boxed_2595_; lean_object* v_res_2596_; 
v_b_boxed_2595_ = lean_unbox(v_b_2594_);
v_res_2596_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_2593_, v_b_boxed_2595_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__1(lean_object* v_p_2597_, lean_object* v_toBind_2598_, lean_object* v___f_2599_, lean_object* v_v_2600_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2601_ = lean_apply_1(v_p_2597_, v_v_2600_);
v___x_2602_ = lean_apply_4(v_toBind_2598_, lean_box(0), lean_box(0), v___x_2601_, v___f_2599_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg(lean_object* v_inst_2603_, lean_object* v_a_2604_, lean_object* v_p_2605_){
_start:
{
lean_object* v_toApplicative_2606_; lean_object* v_toBind_2607_; lean_object* v_toPure_2608_; lean_object* v___f_2609_; lean_object* v___f_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v_toApplicative_2606_ = lean_ctor_get(v_inst_2603_, 0);
v_toBind_2607_ = lean_ctor_get(v_inst_2603_, 1);
lean_inc_n(v_toBind_2607_, 2);
v_toPure_2608_ = lean_ctor_get(v_toApplicative_2606_, 1);
lean_inc(v_toPure_2608_);
v___f_2609_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2609_, 0, v_toPure_2608_);
lean_inc_ref(v___f_2609_);
v___f_2610_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2610_, 0, v_p_2605_);
lean_closure_set(v___f_2610_, 1, v_toBind_2607_);
lean_closure_set(v___f_2610_, 2, v___f_2609_);
v___x_2611_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2603_, v_a_2604_, v___f_2610_);
v___x_2612_ = lean_apply_4(v_toBind_2607_, lean_box(0), lean_box(0), v___x_2611_, v___f_2609_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM(lean_object* v_00_u03b1_2613_, lean_object* v_m_2614_, lean_object* v_inst_2615_, lean_object* v_a_2616_, lean_object* v_p_2617_){
_start:
{
lean_object* v_toApplicative_2618_; lean_object* v_toBind_2619_; lean_object* v_toPure_2620_; lean_object* v___f_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v_toApplicative_2618_ = lean_ctor_get(v_inst_2615_, 0);
v_toBind_2619_ = lean_ctor_get(v_inst_2615_, 1);
lean_inc_n(v_toBind_2619_, 2);
v_toPure_2620_ = lean_ctor_get(v_toApplicative_2618_, 1);
lean_inc(v_toPure_2620_);
v___f_2621_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2621_, 0, v_toPure_2620_);
lean_inc_ref(v___f_2621_);
v___f_2622_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2622_, 0, v_p_2617_);
lean_closure_set(v___f_2622_, 1, v_toBind_2619_);
lean_closure_set(v___f_2622_, 2, v___f_2621_);
v___x_2623_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2615_, v_a_2616_, v___f_2622_);
v___x_2624_ = lean_apply_4(v_toBind_2619_, lean_box(0), lean_box(0), v___x_2623_, v___f_2621_);
return v___x_2624_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg___lam__0(lean_object* v_p_2625_, lean_object* v_x_2626_){
_start:
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = lean_apply_1(v_p_2625_, v_x_2626_);
v___x_2628_ = lean_unbox(v___x_2627_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___lam__0___boxed(lean_object* v_p_2629_, lean_object* v_x_2630_){
_start:
{
uint8_t v_res_2631_; lean_object* v_r_2632_; 
v_res_2631_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_2629_, v_x_2630_);
v_r_2632_ = lean_box(v_res_2631_);
return v_r_2632_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg(lean_object* v_a_2633_, lean_object* v_p_2634_){
_start:
{
lean_object* v___f_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v___f_2635_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2635_, 0, v_p_2634_);
v___x_2636_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2637_ = l_Lean_PersistentArray_anyM___redArg(v___x_2636_, v_a_2633_, v___f_2635_);
v___x_2638_ = lean_unbox(v___x_2637_);
lean_dec(v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___boxed(lean_object* v_a_2639_, lean_object* v_p_2640_){
_start:
{
uint8_t v_res_2641_; lean_object* v_r_2642_; 
v_res_2641_ = l_Lean_PersistentArray_any___redArg(v_a_2639_, v_p_2640_);
v_r_2642_ = lean_box(v_res_2641_);
return v_r_2642_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any(lean_object* v_00_u03b1_2643_, lean_object* v_a_2644_, lean_object* v_p_2645_){
_start:
{
lean_object* v___f_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___f_2646_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2646_, 0, v_p_2645_);
v___x_2647_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2648_ = l_Lean_PersistentArray_anyM___redArg(v___x_2647_, v_a_2644_, v___f_2646_);
v___x_2649_ = lean_unbox(v___x_2648_);
lean_dec(v___x_2648_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___boxed(lean_object* v_00_u03b1_2650_, lean_object* v_a_2651_, lean_object* v_p_2652_){
_start:
{
uint8_t v_res_2653_; lean_object* v_r_2654_; 
v_res_2653_ = l_Lean_PersistentArray_any(v_00_u03b1_2650_, v_a_2651_, v_p_2652_);
v_r_2654_ = lean_box(v_res_2653_);
return v_r_2654_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg___lam__0(lean_object* v_p_2655_, lean_object* v_x_2656_){
_start:
{
lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2657_ = lean_apply_1(v_p_2655_, v_x_2656_);
v___x_2658_ = lean_unbox(v___x_2657_);
if (v___x_2658_ == 0)
{
uint8_t v___x_2659_; 
v___x_2659_ = 1;
return v___x_2659_;
}
else
{
uint8_t v___x_2660_; 
v___x_2660_ = 0;
return v___x_2660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___lam__0___boxed(lean_object* v_p_2661_, lean_object* v_x_2662_){
_start:
{
uint8_t v_res_2663_; lean_object* v_r_2664_; 
v_res_2663_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_2661_, v_x_2662_);
v_r_2664_ = lean_box(v_res_2663_);
return v_r_2664_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg(lean_object* v_a_2665_, lean_object* v_p_2666_){
_start:
{
lean_object* v___f_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___f_2667_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2667_, 0, v_p_2666_);
v___x_2668_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2669_ = l_Lean_PersistentArray_anyM___redArg(v___x_2668_, v_a_2665_, v___f_2667_);
v___x_2670_ = lean_unbox(v___x_2669_);
lean_dec(v___x_2669_);
if (v___x_2670_ == 0)
{
uint8_t v___x_2671_; 
v___x_2671_ = 1;
return v___x_2671_;
}
else
{
uint8_t v___x_2672_; 
v___x_2672_ = 0;
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___boxed(lean_object* v_a_2673_, lean_object* v_p_2674_){
_start:
{
uint8_t v_res_2675_; lean_object* v_r_2676_; 
v_res_2675_ = l_Lean_PersistentArray_all___redArg(v_a_2673_, v_p_2674_);
v_r_2676_ = lean_box(v_res_2675_);
return v_r_2676_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all(lean_object* v_00_u03b1_2677_, lean_object* v_a_2678_, lean_object* v_p_2679_){
_start:
{
lean_object* v___f_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; 
v___f_2680_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2680_, 0, v_p_2679_);
v___x_2681_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2682_ = l_Lean_PersistentArray_anyM___redArg(v___x_2681_, v_a_2678_, v___f_2680_);
v___x_2683_ = lean_unbox(v___x_2682_);
lean_dec(v___x_2682_);
if (v___x_2683_ == 0)
{
uint8_t v___x_2684_; 
v___x_2684_ = 1;
return v___x_2684_;
}
else
{
uint8_t v___x_2685_; 
v___x_2685_ = 0;
return v___x_2685_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___boxed(lean_object* v_00_u03b1_2686_, lean_object* v_a_2687_, lean_object* v_p_2688_){
_start:
{
uint8_t v_res_2689_; lean_object* v_r_2690_; 
v_res_2689_ = l_Lean_PersistentArray_all(v_00_u03b1_2686_, v_a_2687_, v_p_2688_);
v_r_2690_ = lean_box(v_res_2689_);
return v_r_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__0(lean_object* v_cs_2691_){
_start:
{
lean_object* v___x_2692_; 
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_cs_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__2(lean_object* v_vs_2693_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_vs_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg(lean_object* v_inst_2697_, lean_object* v_f_2698_, lean_object* v_x_2699_){
_start:
{
if (lean_obj_tag(v_x_2699_) == 0)
{
lean_object* v_toApplicative_2700_; lean_object* v_toFunctor_2701_; lean_object* v_cs_2702_; lean_object* v_map_2703_; lean_object* v___f_2704_; lean_object* v___f_2705_; size_t v_sz_2706_; size_t v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v_toApplicative_2700_ = lean_ctor_get(v_inst_2697_, 0);
v_toFunctor_2701_ = lean_ctor_get(v_toApplicative_2700_, 0);
v_cs_2702_ = lean_ctor_get(v_x_2699_, 0);
lean_inc_ref(v_cs_2702_);
lean_dec_ref(v_x_2699_);
v_map_2703_ = lean_ctor_get(v_toFunctor_2701_, 0);
lean_inc(v_map_2703_);
v___f_2704_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__0));
lean_inc_ref(v_inst_2697_);
v___f_2705_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapMAux___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2705_, 0, v_inst_2697_);
lean_closure_set(v___f_2705_, 1, v_f_2698_);
v_sz_2706_ = lean_array_size(v_cs_2702_);
v___x_2707_ = ((size_t)0ULL);
v___x_2708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2697_, v___f_2705_, v_sz_2706_, v___x_2707_, v_cs_2702_);
v___x_2709_ = lean_apply_4(v_map_2703_, lean_box(0), lean_box(0), v___f_2704_, v___x_2708_);
return v___x_2709_;
}
else
{
lean_object* v_toApplicative_2710_; lean_object* v_toFunctor_2711_; lean_object* v_vs_2712_; lean_object* v_map_2713_; lean_object* v___f_2714_; size_t v_sz_2715_; size_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_toApplicative_2710_ = lean_ctor_get(v_inst_2697_, 0);
v_toFunctor_2711_ = lean_ctor_get(v_toApplicative_2710_, 0);
v_vs_2712_ = lean_ctor_get(v_x_2699_, 0);
lean_inc_ref(v_vs_2712_);
lean_dec_ref(v_x_2699_);
v_map_2713_ = lean_ctor_get(v_toFunctor_2711_, 0);
lean_inc(v_map_2713_);
v___f_2714_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__1));
v_sz_2715_ = lean_array_size(v_vs_2712_);
v___x_2716_ = ((size_t)0ULL);
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2697_, v_f_2698_, v_sz_2715_, v___x_2716_, v_vs_2712_);
v___x_2718_ = lean_apply_4(v_map_2713_, lean_box(0), lean_box(0), v___f_2714_, v___x_2717_);
return v___x_2718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__1(lean_object* v_inst_2719_, lean_object* v_f_2720_, lean_object* v_c_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2719_, v_f_2720_, v_c_2721_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux(lean_object* v_00_u03b1_2723_, lean_object* v_m_2724_, lean_object* v_inst_2725_, lean_object* v_00_u03b2_2726_, lean_object* v_f_2727_, lean_object* v_x_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2725_, v_f_2727_, v_x_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0(lean_object* v_root_2730_, lean_object* v_size_2731_, size_t v_shift_2732_, lean_object* v_tailOff_2733_, lean_object* v_toPure_2734_, lean_object* v_tail_2735_){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2736_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2736_, 0, v_root_2730_);
lean_ctor_set(v___x_2736_, 1, v_tail_2735_);
lean_ctor_set(v___x_2736_, 2, v_size_2731_);
lean_ctor_set(v___x_2736_, 3, v_tailOff_2733_);
lean_ctor_set_usize(v___x_2736_, 4, v_shift_2732_);
v___x_2737_ = lean_apply_2(v_toPure_2734_, lean_box(0), v___x_2736_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(lean_object* v_root_2738_, lean_object* v_size_2739_, lean_object* v_shift_2740_, lean_object* v_tailOff_2741_, lean_object* v_toPure_2742_, lean_object* v_tail_2743_){
_start:
{
size_t v_shift_boxed_2744_; lean_object* v_res_2745_; 
v_shift_boxed_2744_ = lean_unbox_usize(v_shift_2740_);
lean_dec(v_shift_2740_);
v_res_2745_ = l_Lean_PersistentArray_mapM___redArg___lam__0(v_root_2738_, v_size_2739_, v_shift_boxed_2744_, v_tailOff_2741_, v_toPure_2742_, v_tail_2743_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1(lean_object* v_size_2746_, size_t v_shift_2747_, lean_object* v_tailOff_2748_, lean_object* v_toPure_2749_, lean_object* v_tail_2750_, lean_object* v_inst_2751_, lean_object* v_f_2752_, lean_object* v_toBind_2753_, lean_object* v_root_2754_){
_start:
{
lean_object* v___x_2755_; lean_object* v___f_2756_; size_t v_sz_2757_; size_t v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2755_ = lean_box_usize(v_shift_2747_);
v___f_2756_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2756_, 0, v_root_2754_);
lean_closure_set(v___f_2756_, 1, v_size_2746_);
lean_closure_set(v___f_2756_, 2, v___x_2755_);
lean_closure_set(v___f_2756_, 3, v_tailOff_2748_);
lean_closure_set(v___f_2756_, 4, v_toPure_2749_);
v_sz_2757_ = lean_array_size(v_tail_2750_);
v___x_2758_ = ((size_t)0ULL);
v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2751_, v_f_2752_, v_sz_2757_, v___x_2758_, v_tail_2750_);
v___x_2760_ = lean_apply_4(v_toBind_2753_, lean_box(0), lean_box(0), v___x_2759_, v___f_2756_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(lean_object* v_size_2761_, lean_object* v_shift_2762_, lean_object* v_tailOff_2763_, lean_object* v_toPure_2764_, lean_object* v_tail_2765_, lean_object* v_inst_2766_, lean_object* v_f_2767_, lean_object* v_toBind_2768_, lean_object* v_root_2769_){
_start:
{
size_t v_shift_boxed_2770_; lean_object* v_res_2771_; 
v_shift_boxed_2770_ = lean_unbox_usize(v_shift_2762_);
lean_dec(v_shift_2762_);
v_res_2771_ = l_Lean_PersistentArray_mapM___redArg___lam__1(v_size_2761_, v_shift_boxed_2770_, v_tailOff_2763_, v_toPure_2764_, v_tail_2765_, v_inst_2766_, v_f_2767_, v_toBind_2768_, v_root_2769_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object* v_inst_2772_, lean_object* v_f_2773_, lean_object* v_t_2774_){
_start:
{
lean_object* v_toApplicative_2775_; lean_object* v_toBind_2776_; lean_object* v_root_2777_; lean_object* v_tail_2778_; lean_object* v_size_2779_; size_t v_shift_2780_; lean_object* v_tailOff_2781_; lean_object* v_toPure_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___f_2785_; lean_object* v___x_2786_; 
v_toApplicative_2775_ = lean_ctor_get(v_inst_2772_, 0);
v_toBind_2776_ = lean_ctor_get(v_inst_2772_, 1);
lean_inc_n(v_toBind_2776_, 2);
v_root_2777_ = lean_ctor_get(v_t_2774_, 0);
lean_inc_ref(v_root_2777_);
v_tail_2778_ = lean_ctor_get(v_t_2774_, 1);
lean_inc_ref(v_tail_2778_);
v_size_2779_ = lean_ctor_get(v_t_2774_, 2);
lean_inc(v_size_2779_);
v_shift_2780_ = lean_ctor_get_usize(v_t_2774_, 4);
v_tailOff_2781_ = lean_ctor_get(v_t_2774_, 3);
lean_inc(v_tailOff_2781_);
lean_dec_ref(v_t_2774_);
v_toPure_2782_ = lean_ctor_get(v_toApplicative_2775_, 1);
lean_inc(v_toPure_2782_);
lean_inc(v_f_2773_);
lean_inc_ref(v_inst_2772_);
v___x_2783_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2772_, v_f_2773_, v_root_2777_);
v___x_2784_ = lean_box_usize(v_shift_2780_);
v___f_2785_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2785_, 0, v_size_2779_);
lean_closure_set(v___f_2785_, 1, v___x_2784_);
lean_closure_set(v___f_2785_, 2, v_tailOff_2781_);
lean_closure_set(v___f_2785_, 3, v_toPure_2782_);
lean_closure_set(v___f_2785_, 4, v_tail_2778_);
lean_closure_set(v___f_2785_, 5, v_inst_2772_);
lean_closure_set(v___f_2785_, 6, v_f_2773_);
lean_closure_set(v___f_2785_, 7, v_toBind_2776_);
v___x_2786_ = lean_apply_4(v_toBind_2776_, lean_box(0), lean_box(0), v___x_2783_, v___f_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM(lean_object* v_00_u03b1_2787_, lean_object* v_m_2788_, lean_object* v_inst_2789_, lean_object* v_00_u03b2_2790_, lean_object* v_f_2791_, lean_object* v_t_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Lean_PersistentArray_mapM___redArg(v_inst_2789_, v_f_2791_, v_t_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg___lam__0(lean_object* v_f_2794_, lean_object* v_x_2795_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = lean_apply_1(v_f_2794_, v_x_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg(lean_object* v_f_2797_, lean_object* v_t_2798_){
_start:
{
lean_object* v___f_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___f_2799_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2799_, 0, v_f_2797_);
v___x_2800_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2801_ = l_Lean_PersistentArray_mapM___redArg(v___x_2800_, v___f_2799_, v_t_2798_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map(lean_object* v_00_u03b1_2802_, lean_object* v_00_u03b2_2803_, lean_object* v_f_2804_, lean_object* v_t_2805_){
_start:
{
lean_object* v___f_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___f_2806_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2806_, 0, v_f_2804_);
v___x_2807_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2808_ = l_Lean_PersistentArray_mapM___redArg(v___x_2807_, v___f_2806_, v_t_2805_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg(lean_object* v_x_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_){
_start:
{
if (lean_obj_tag(v_x_2809_) == 0)
{
lean_object* v_cs_2812_; lean_object* v_numNodes_2813_; lean_object* v_depth_2814_; lean_object* v_tailSize_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2837_; 
v_cs_2812_ = lean_ctor_get(v_x_2809_, 0);
v_numNodes_2813_ = lean_ctor_get(v_x_2810_, 0);
v_depth_2814_ = lean_ctor_get(v_x_2810_, 1);
v_tailSize_2815_ = lean_ctor_get(v_x_2810_, 2);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_x_2810_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2817_ = v_x_2810_;
v_isShared_2818_ = v_isSharedCheck_2837_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_tailSize_2815_);
lean_inc(v_depth_2814_);
lean_inc(v_numNodes_2813_);
lean_dec(v_x_2810_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2837_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___y_2822_; uint8_t v___x_2836_; 
v___x_2819_ = lean_unsigned_to_nat(1u);
v___x_2820_ = lean_nat_add(v_numNodes_2813_, v___x_2819_);
lean_dec(v_numNodes_2813_);
v___x_2836_ = lean_nat_dec_le(v_x_2811_, v_depth_2814_);
if (v___x_2836_ == 0)
{
lean_dec(v_depth_2814_);
lean_inc(v_x_2811_);
v___y_2822_ = v_x_2811_;
goto v___jp_2821_;
}
else
{
v___y_2822_ = v_depth_2814_;
goto v___jp_2821_;
}
v___jp_2821_:
{
lean_object* v___x_2824_; 
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v___y_2822_);
lean_ctor_set(v___x_2817_, 0, v___x_2820_);
v___x_2824_ = v___x_2817_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2835_, 1, v___y_2822_);
lean_ctor_set(v_reuseFailAlloc_2835_, 2, v_tailSize_2815_);
v___x_2824_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2825_ = lean_unsigned_to_nat(0u);
v___x_2826_ = lean_array_get_size(v_cs_2812_);
v___x_2827_ = lean_nat_dec_lt(v___x_2825_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_dec(v_x_2811_);
return v___x_2824_;
}
else
{
uint8_t v___x_2828_; 
v___x_2828_ = lean_nat_dec_le(v___x_2826_, v___x_2826_);
if (v___x_2828_ == 0)
{
if (v___x_2827_ == 0)
{
lean_dec(v_x_2811_);
return v___x_2824_;
}
else
{
size_t v___x_2829_; size_t v___x_2830_; lean_object* v___x_2831_; 
v___x_2829_ = ((size_t)0ULL);
v___x_2830_ = lean_usize_of_nat(v___x_2826_);
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2811_, v_cs_2812_, v___x_2829_, v___x_2830_, v___x_2824_);
lean_dec(v_x_2811_);
return v___x_2831_;
}
}
else
{
size_t v___x_2832_; size_t v___x_2833_; lean_object* v___x_2834_; 
v___x_2832_ = ((size_t)0ULL);
v___x_2833_ = lean_usize_of_nat(v___x_2826_);
v___x_2834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2811_, v_cs_2812_, v___x_2832_, v___x_2833_, v___x_2824_);
lean_dec(v_x_2811_);
return v___x_2834_;
}
}
}
}
}
}
else
{
lean_object* v_numNodes_2838_; lean_object* v_depth_2839_; lean_object* v_tailSize_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2853_; 
v_numNodes_2838_ = lean_ctor_get(v_x_2810_, 0);
v_depth_2839_ = lean_ctor_get(v_x_2810_, 1);
v_tailSize_2840_ = lean_ctor_get(v_x_2810_, 2);
v_isSharedCheck_2853_ = !lean_is_exclusive(v_x_2810_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2842_ = v_x_2810_;
v_isShared_2843_ = v_isSharedCheck_2853_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_tailSize_2840_);
lean_inc(v_depth_2839_);
lean_inc(v_numNodes_2838_);
lean_dec(v_x_2810_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2853_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v___x_2844_ = lean_unsigned_to_nat(1u);
v___x_2845_ = lean_nat_add(v_numNodes_2838_, v___x_2844_);
lean_dec(v_numNodes_2838_);
v___x_2846_ = lean_nat_dec_le(v_x_2811_, v_depth_2839_);
if (v___x_2846_ == 0)
{
lean_object* v___x_2848_; 
lean_dec(v_depth_2839_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 1, v_x_2811_);
lean_ctor_set(v___x_2842_, 0, v___x_2845_);
v___x_2848_ = v___x_2842_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2845_);
lean_ctor_set(v_reuseFailAlloc_2849_, 1, v_x_2811_);
lean_ctor_set(v_reuseFailAlloc_2849_, 2, v_tailSize_2840_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
else
{
lean_object* v___x_2851_; 
lean_dec(v_x_2811_);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_2845_);
v___x_2851_ = v___x_2842_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2845_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_depth_2839_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v_tailSize_2840_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(lean_object* v_x_2854_, lean_object* v_as_2855_, size_t v_i_2856_, size_t v_stop_2857_, lean_object* v_b_2858_){
_start:
{
uint8_t v___x_2859_; 
v___x_2859_ = lean_usize_dec_eq(v_i_2856_, v_stop_2857_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; size_t v___x_2864_; size_t v___x_2865_; 
v___x_2860_ = lean_array_uget_borrowed(v_as_2855_, v_i_2856_);
v___x_2861_ = lean_unsigned_to_nat(1u);
v___x_2862_ = lean_nat_add(v_x_2854_, v___x_2861_);
v___x_2863_ = l_Lean_PersistentArray_collectStats___redArg(v___x_2860_, v_b_2858_, v___x_2862_);
v___x_2864_ = ((size_t)1ULL);
v___x_2865_ = lean_usize_add(v_i_2856_, v___x_2864_);
v_i_2856_ = v___x_2865_;
v_b_2858_ = v___x_2863_;
goto _start;
}
else
{
return v_b_2858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg___boxed(lean_object* v_x_2867_, lean_object* v_as_2868_, lean_object* v_i_2869_, lean_object* v_stop_2870_, lean_object* v_b_2871_){
_start:
{
size_t v_i_boxed_2872_; size_t v_stop_boxed_2873_; lean_object* v_res_2874_; 
v_i_boxed_2872_ = lean_unbox_usize(v_i_2869_);
lean_dec(v_i_2869_);
v_stop_boxed_2873_ = lean_unbox_usize(v_stop_2870_);
lean_dec(v_stop_2870_);
v_res_2874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2867_, v_as_2868_, v_i_boxed_2872_, v_stop_boxed_2873_, v_b_2871_);
lean_dec_ref(v_as_2868_);
lean_dec(v_x_2867_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg___boxed(lean_object* v_x_2875_, lean_object* v_x_2876_, lean_object* v_x_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2875_, v_x_2876_, v_x_2877_);
lean_dec_ref(v_x_2875_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats(lean_object* v_00_u03b1_2879_, lean_object* v_x_2880_, lean_object* v_x_2881_, lean_object* v_x_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2880_, v_x_2881_, v_x_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___boxed(lean_object* v_00_u03b1_2884_, lean_object* v_x_2885_, lean_object* v_x_2886_, lean_object* v_x_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_PersistentArray_collectStats(v_00_u03b1_2884_, v_x_2885_, v_x_2886_, v_x_2887_);
lean_dec_ref(v_x_2885_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(lean_object* v_00_u03b1_2889_, lean_object* v_x_2890_, lean_object* v_as_2891_, size_t v_i_2892_, size_t v_stop_2893_, lean_object* v_b_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2890_, v_as_2891_, v_i_2892_, v_stop_2893_, v_b_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2896_, lean_object* v_x_2897_, lean_object* v_as_2898_, lean_object* v_i_2899_, lean_object* v_stop_2900_, lean_object* v_b_2901_){
_start:
{
size_t v_i_boxed_2902_; size_t v_stop_boxed_2903_; lean_object* v_res_2904_; 
v_i_boxed_2902_ = lean_unbox_usize(v_i_2899_);
lean_dec(v_i_2899_);
v_stop_boxed_2903_ = lean_unbox_usize(v_stop_2900_);
lean_dec(v_stop_2900_);
v_res_2904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(v_00_u03b1_2896_, v_x_2897_, v_as_2898_, v_i_boxed_2902_, v_stop_boxed_2903_, v_b_2901_);
lean_dec_ref(v_as_2898_);
lean_dec(v_x_2897_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg(lean_object* v_r_2905_){
_start:
{
lean_object* v_root_2906_; lean_object* v_tail_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v_root_2906_ = lean_ctor_get(v_r_2905_, 0);
v_tail_2907_ = lean_ctor_get(v_r_2905_, 1);
v___x_2908_ = lean_unsigned_to_nat(0u);
v___x_2909_ = lean_array_get_size(v_tail_2907_);
v___x_2910_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2908_);
lean_ctor_set(v___x_2910_, 1, v___x_2908_);
lean_ctor_set(v___x_2910_, 2, v___x_2909_);
v___x_2911_ = l_Lean_PersistentArray_collectStats___redArg(v_root_2906_, v___x_2910_, v___x_2908_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg___boxed(lean_object* v_r_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_PersistentArray_stats___redArg(v_r_2912_);
lean_dec_ref(v_r_2912_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats(lean_object* v_00_u03b1_2914_, lean_object* v_r_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_Lean_PersistentArray_stats___redArg(v_r_2915_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___boxed(lean_object* v_00_u03b1_2917_, lean_object* v_r_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_PersistentArray_stats(v_00_u03b1_2917_, v_r_2918_);
lean_dec_ref(v_r_2918_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Stats_toString(lean_object* v_s_2924_){
_start:
{
lean_object* v_numNodes_2925_; lean_object* v_depth_2926_; lean_object* v_tailSize_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v_numNodes_2925_ = lean_ctor_get(v_s_2924_, 0);
lean_inc(v_numNodes_2925_);
v_depth_2926_ = lean_ctor_get(v_s_2924_, 1);
lean_inc(v_depth_2926_);
v_tailSize_2927_ = lean_ctor_get(v_s_2924_, 2);
lean_inc(v_tailSize_2927_);
lean_dec_ref(v_s_2924_);
v___x_2928_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__0));
v___x_2929_ = l_Nat_reprFast(v_numNodes_2925_);
v___x_2930_ = lean_string_append(v___x_2928_, v___x_2929_);
lean_dec_ref(v___x_2929_);
v___x_2931_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__1));
v___x_2932_ = lean_string_append(v___x_2930_, v___x_2931_);
v___x_2933_ = l_Nat_reprFast(v_depth_2926_);
v___x_2934_ = lean_string_append(v___x_2932_, v___x_2933_);
lean_dec_ref(v___x_2933_);
v___x_2935_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__2));
v___x_2936_ = lean_string_append(v___x_2934_, v___x_2935_);
v___x_2937_ = l_Nat_reprFast(v_tailSize_2927_);
v___x_2938_ = lean_string_append(v___x_2936_, v___x_2937_);
lean_dec_ref(v___x_2937_);
v___x_2939_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__3));
v___x_2940_ = lean_string_append(v___x_2938_, v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(lean_object* v_v_2943_, lean_object* v_j_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v_zero_2946_; uint8_t v_isZero_2947_; 
v_zero_2946_ = lean_unsigned_to_nat(0u);
v_isZero_2947_ = lean_nat_dec_eq(v_j_2944_, v_zero_2946_);
if (v_isZero_2947_ == 1)
{
lean_dec(v_j_2944_);
lean_dec(v_v_2943_);
return v_a_2945_;
}
else
{
lean_object* v_one_2948_; lean_object* v_n_2949_; lean_object* v___x_2950_; 
v_one_2948_ = lean_unsigned_to_nat(1u);
v_n_2949_ = lean_nat_sub(v_j_2944_, v_one_2948_);
lean_dec(v_j_2944_);
lean_inc(v_v_2943_);
v___x_2950_ = l_Lean_PersistentArray_push___redArg(v_a_2945_, v_v_2943_);
v_j_2944_ = v_n_2949_;
v_a_2945_ = v___x_2950_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_mkPersistentArray___redArg___closed__0(void){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_PersistentArray_empty(lean_box(0));
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray___redArg(lean_object* v_n_2953_, lean_object* v_v_2954_){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_obj_once(&l_Lean_mkPersistentArray___redArg___closed__0, &l_Lean_mkPersistentArray___redArg___closed__0_once, _init_l_Lean_mkPersistentArray___redArg___closed__0);
v___x_2956_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2954_, v_n_2953_, v___x_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray(lean_object* v_00_u03b1_2957_, lean_object* v_n_2958_, lean_object* v_v_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_mkPersistentArray___redArg(v_n_2958_, v_v_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(lean_object* v_00_u03b1_2961_, lean_object* v_v_2962_, lean_object* v_n_2963_, lean_object* v_j_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2962_, v_j_2964_, v_a_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(lean_object* v_00_u03b1_2968_, lean_object* v_v_2969_, lean_object* v_n_2970_, lean_object* v_j_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(v_00_u03b1_2968_, v_v_2969_, v_n_2970_, v_j_2971_, v_a_2972_, v_a_2973_);
lean_dec(v_n_2970_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray___redArg(lean_object* v_n_2975_, lean_object* v_v_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_mkPersistentArray___redArg(v_n_2975_, v_v_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray(lean_object* v_00_u03b1_2978_, lean_object* v_n_2979_, lean_object* v_v_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_mkPersistentArray___redArg(v_n_2979_, v_v_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
if (lean_obj_tag(v_a_2982_) == 0)
{
return v_a_2983_;
}
else
{
lean_object* v_head_2984_; lean_object* v_tail_2985_; lean_object* v___x_2986_; 
v_head_2984_ = lean_ctor_get(v_a_2982_, 0);
lean_inc(v_head_2984_);
v_tail_2985_ = lean_ctor_get(v_a_2982_, 1);
lean_inc(v_tail_2985_);
lean_dec_ref(v_a_2982_);
v___x_2986_ = l_Lean_PersistentArray_push___redArg(v_a_2983_, v_head_2984_);
v_a_2982_ = v_tail_2985_;
v_a_2983_ = v___x_2986_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop(lean_object* v_00_u03b1_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(v_a_2989_, v_a_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_List_toPArray_x27___redArg(lean_object* v_xs_2992_){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2993_ = lean_unsigned_to_nat(32u);
v___x_2994_ = lean_mk_empty_array_with_capacity(v___x_2993_);
lean_dec_ref(v___x_2994_);
v___x_2995_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
v___x_2996_ = l___private_Lean_Data_PersistentArray_0__List_toPArray_x27_loop___redArg(v_xs_2992_, v___x_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_List_toPArray_x27(lean_object* v_00_u03b1_2997_, lean_object* v_xs_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_List_toPArray_x27___redArg(v_xs_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27___redArg(lean_object* v_xs_3000_){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; 
v___x_3001_ = lean_obj_once(&l_Lean_mkPersistentArray___redArg___closed__0, &l_Lean_mkPersistentArray___redArg___closed__0_once, _init_l_Lean_mkPersistentArray___redArg___closed__0);
v___x_3002_ = lean_unsigned_to_nat(0u);
v___x_3003_ = lean_array_get_size(v_xs_3000_);
v___x_3004_ = lean_nat_dec_lt(v___x_3002_, v___x_3003_);
if (v___x_3004_ == 0)
{
return v___x_3001_;
}
else
{
uint8_t v___x_3005_; 
v___x_3005_ = lean_nat_dec_le(v___x_3003_, v___x_3003_);
if (v___x_3005_ == 0)
{
if (v___x_3004_ == 0)
{
return v___x_3001_;
}
else
{
size_t v___x_3006_; size_t v___x_3007_; lean_object* v___x_3008_; 
v___x_3006_ = ((size_t)0ULL);
v___x_3007_ = lean_usize_of_nat(v___x_3003_);
v___x_3008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_3000_, v___x_3006_, v___x_3007_, v___x_3001_);
return v___x_3008_;
}
}
else
{
size_t v___x_3009_; size_t v___x_3010_; lean_object* v___x_3011_; 
v___x_3009_ = ((size_t)0ULL);
v___x_3010_ = lean_usize_of_nat(v___x_3003_);
v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_3000_, v___x_3009_, v___x_3010_, v___x_3001_);
return v___x_3011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27___redArg___boxed(lean_object* v_xs_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Array_toPArray_x27___redArg(v_xs_3012_);
lean_dec_ref(v_xs_3012_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27(lean_object* v_00_u03b1_3014_, lean_object* v_xs_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l_Array_toPArray_x27___redArg(v_xs_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Array_toPArray_x27___boxed(lean_object* v_00_u03b1_3017_, lean_object* v_xs_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Array_toPArray_x27(v_00_u03b1_3017_, v_xs_3018_);
lean_dec_ref(v_xs_3018_);
return v_res_3019_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Fold(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_PersistentArray(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
