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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___boxed(lean_object*, lean_object*);
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
size_t v_x_94__boxed_160_; size_t v_x_95__boxed_161_; lean_object* v_res_162_; 
v_x_94__boxed_160_ = lean_unbox_usize(v_x_158_);
lean_dec(v_x_158_);
v_x_95__boxed_161_ = lean_unbox_usize(v_x_159_);
lean_dec(v_x_159_);
v_res_162_ = l_Lean_PersistentArray_getAux___redArg(v_inst_156_, v_x_157_, v_x_94__boxed_160_, v_x_95__boxed_161_);
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
size_t v_x_136__boxed_174_; size_t v_x_137__boxed_175_; lean_object* v_res_176_; 
v_x_136__boxed_174_ = lean_unbox_usize(v_x_172_);
lean_dec(v_x_172_);
v_x_137__boxed_175_ = lean_unbox_usize(v_x_173_);
lean_dec(v_x_173_);
v_res_176_ = l_Lean_PersistentArray_getAux(v_00_u03b1_169_, v_inst_170_, v_x_171_, v_x_136__boxed_174_, v_x_137__boxed_175_);
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
size_t v_x_79__boxed_260_; size_t v_x_80__boxed_261_; lean_object* v_res_262_; 
v_x_79__boxed_260_ = lean_unbox_usize(v_x_257_);
lean_dec(v_x_257_);
v_x_80__boxed_261_ = lean_unbox_usize(v_x_258_);
lean_dec(v_x_258_);
v_res_262_ = l_Lean_PersistentArray_setAux___redArg(v_x_256_, v_x_79__boxed_260_, v_x_80__boxed_261_, v_x_259_);
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
size_t v_x_149__boxed_274_; size_t v_x_150__boxed_275_; lean_object* v_res_276_; 
v_x_149__boxed_274_ = lean_unbox_usize(v_x_271_);
lean_dec(v_x_271_);
v_x_150__boxed_275_ = lean_unbox_usize(v_x_272_);
lean_dec(v_x_272_);
v_res_276_ = l_Lean_PersistentArray_setAux(v_00_u03b1_269_, v_x_270_, v_x_149__boxed_274_, v_x_150__boxed_275_, v_x_273_);
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
size_t v_x_96__boxed_363_; size_t v_x_97__boxed_364_; lean_object* v_res_365_; 
v_x_96__boxed_363_ = lean_unbox_usize(v_x_361_);
lean_dec(v_x_361_);
v_x_97__boxed_364_ = lean_unbox_usize(v_x_362_);
lean_dec(v_x_362_);
v_res_365_ = l_Lean_PersistentArray_modifyAux___redArg(v_f_359_, v_x_360_, v_x_96__boxed_363_, v_x_97__boxed_364_);
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
size_t v_x_174__boxed_379_; size_t v_x_175__boxed_380_; lean_object* v_res_381_; 
v_x_174__boxed_379_ = lean_unbox_usize(v_x_377_);
lean_dec(v_x_377_);
v_x_175__boxed_380_ = lean_unbox_usize(v_x_378_);
lean_dec(v_x_378_);
v_res_381_ = l_Lean_PersistentArray_modifyAux(v_00_u03b1_373_, v_inst_374_, v_f_375_, v_x_376_, v_x_174__boxed_379_, v_x_175__boxed_380_);
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
size_t v_x_101__boxed_509_; size_t v_x_102__boxed_510_; lean_object* v_res_511_; 
v_x_101__boxed_509_ = lean_unbox_usize(v_x_506_);
lean_dec(v_x_506_);
v_x_102__boxed_510_ = lean_unbox_usize(v_x_507_);
lean_dec(v_x_507_);
v_res_511_ = l_Lean_PersistentArray_insertNewLeaf___redArg(v_x_505_, v_x_101__boxed_509_, v_x_102__boxed_510_, v_x_508_);
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
size_t v_x_195__boxed_523_; size_t v_x_196__boxed_524_; lean_object* v_res_525_; 
v_x_195__boxed_523_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_x_196__boxed_524_ = lean_unbox_usize(v_x_521_);
lean_dec(v_x_521_);
v_res_525_ = l_Lean_PersistentArray_insertNewLeaf(v_00_u03b1_518_, v_x_519_, v_x_195__boxed_523_, v_x_196__boxed_524_, v_x_522_);
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
lean_object* v_root_574_; lean_object* v_tail_575_; lean_object* v_size_576_; size_t v_shift_577_; lean_object* v_tailOff_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_594_; 
v_root_574_ = lean_ctor_get(v_t_572_, 0);
v_tail_575_ = lean_ctor_get(v_t_572_, 1);
v_size_576_ = lean_ctor_get(v_t_572_, 2);
v_shift_577_ = lean_ctor_get_usize(v_t_572_, 4);
v_tailOff_578_ = lean_ctor_get(v_t_572_, 3);
v_isSharedCheck_594_ = !lean_is_exclusive(v_t_572_);
if (v_isSharedCheck_594_ == 0)
{
v___x_580_ = v_t_572_;
v_isShared_581_ = v_isSharedCheck_594_;
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
v_isShared_581_ = v_isSharedCheck_594_;
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
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_root_574_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_593_, 2, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_593_, 3, v_tailOff_578_);
lean_ctor_set_usize(v_reuseFailAlloc_593_, 4, v_shift_577_);
v_r_586_ = v_reuseFailAlloc_593_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_587_ = lean_array_get_size(v___x_582_);
lean_dec_ref(v___x_582_);
v___x_588_ = lean_unsigned_to_nat(32u);
v___x_589_ = lean_nat_dec_lt(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_590_ = l_Lean_PersistentArray_tooBig;
v___x_591_ = lean_nat_dec_le(v___x_590_, v_size_576_);
lean_dec(v_size_576_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_PersistentArray_mkNewTail___redArg(v_r_586_);
return v___x_592_;
}
else
{
return v_r_586_;
}
}
else
{
lean_dec(v_size_576_);
return v_r_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_push(lean_object* v_00_u03b1_595_, lean_object* v_t_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_PersistentArray_push___redArg(v_t_596_, v_a_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_object* v_00_u03b1_599_){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(32u);
v___x_601_ = lean_mk_empty_array_with_capacity(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0(void){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_emptyArray(lean_box(0));
return v___x_602_;
}
}
static lean_object* _init_l_Lean_PersistentArray_popLeaf___redArg___closed__1(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
v___x_604_ = lean_box(0);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf___redArg(lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
lean_object* v_cs_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_657_; 
v_cs_607_ = lean_ctor_get(v_x_606_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v_x_606_);
if (v_isSharedCheck_657_ == 0)
{
v___x_609_ = v_x_606_;
v_isShared_610_ = v_isSharedCheck_657_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_cs_607_);
lean_dec(v_x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_657_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_array_get_size(v_cs_607_);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_nat_dec_eq(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v_idx_615_; lean_object* v_last_616_; lean_object* v___x_617_; lean_object* v_fst_618_; 
v___x_614_ = lean_unsigned_to_nat(1u);
v_idx_615_ = lean_nat_sub(v___x_611_, v___x_614_);
v_last_616_ = lean_array_fget_borrowed(v_cs_607_, v_idx_615_);
lean_inc(v_last_616_);
v___x_617_ = l_Lean_PersistentArray_popLeaf___redArg(v_last_616_);
v_fst_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_fst_618_);
if (lean_obj_tag(v_fst_618_) == 0)
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_idx_615_);
lean_del_object(v___x_609_);
lean_dec_ref(v_cs_607_);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_626_ == 0)
{
lean_object* v_unused_627_; lean_object* v_unused_628_; 
v_unused_627_ = lean_ctor_get(v___x_617_, 1);
lean_dec(v_unused_627_);
v_unused_628_ = lean_ctor_get(v___x_617_, 0);
lean_dec(v_unused_628_);
v___x_620_ = v___x_617_;
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
else
{
lean_dec(v___x_617_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_626_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_624_; 
v___x_622_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 1, v___x_622_);
v___x_624_ = v___x_620_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_fst_618_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_622_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
else
{
lean_object* v_snd_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_654_; 
v_snd_629_ = lean_ctor_get(v___x_617_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v___x_617_, 0);
lean_dec(v_unused_655_);
v___x_631_ = v___x_617_;
v_isShared_632_ = v_isSharedCheck_654_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_snd_629_);
lean_dec(v___x_617_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_654_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v_cs_x27_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_633_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v_cs_x27_634_ = lean_array_fset(v_cs_607_, v_idx_615_, v___x_633_);
v___x_635_ = lean_array_get_size(v_snd_629_);
v___x_636_ = lean_nat_dec_eq(v___x_635_, v___x_612_);
if (v___x_636_ == 0)
{
lean_object* v___x_638_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v_snd_629_);
v___x_638_ = v___x_609_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_snd_629_);
v___x_638_ = v_reuseFailAlloc_643_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = lean_array_fset(v_cs_x27_634_, v_idx_615_, v___x_638_);
lean_dec(v_idx_615_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v___x_639_);
v___x_641_ = v___x_631_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_fst_618_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
else
{
lean_object* v_cs_x27_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
lean_dec(v_snd_629_);
lean_dec(v_idx_615_);
lean_del_object(v___x_609_);
v_cs_x27_644_ = lean_array_pop(v_cs_x27_634_);
v___x_645_ = lean_array_get_size(v_cs_x27_644_);
v___x_646_ = lean_nat_dec_eq(v___x_645_, v___x_612_);
if (v___x_646_ == 0)
{
lean_object* v___x_648_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v_cs_x27_644_);
v___x_648_ = v___x_631_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_fst_618_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_cs_x27_644_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
else
{
lean_object* v___x_650_; lean_object* v___x_652_; 
lean_dec_ref(v_cs_x27_644_);
v___x_650_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v___x_650_);
v___x_652_ = v___x_631_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_fst_618_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
else
{
lean_object* v___x_656_; 
lean_del_object(v___x_609_);
lean_dec_ref(v_cs_607_);
v___x_656_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__1, &l_Lean_PersistentArray_popLeaf___redArg___closed__1_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__1);
return v___x_656_;
}
}
}
else
{
lean_object* v_vs_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_vs_658_ = lean_ctor_get(v_x_606_, 0);
lean_inc_ref(v_vs_658_);
lean_dec_ref_known(v_x_606_, 1);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v_vs_658_);
v___x_660_ = lean_obj_once(&l_Lean_PersistentArray_popLeaf___redArg___closed__0, &l_Lean_PersistentArray_popLeaf___redArg___closed__0_once, _init_l_Lean_PersistentArray_popLeaf___redArg___closed__0);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
return v___x_661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_popLeaf(lean_object* v_00_u03b1_662_, lean_object* v_x_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_PersistentArray_popLeaf___redArg(v_x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop___redArg(lean_object* v_t_665_){
_start:
{
lean_object* v_root_666_; lean_object* v_tail_667_; lean_object* v_size_668_; size_t v_shift_669_; lean_object* v_tailOff_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_root_666_ = lean_ctor_get(v_t_665_, 0);
v_tail_667_ = lean_ctor_get(v_t_665_, 1);
v_size_668_ = lean_ctor_get(v_t_665_, 2);
v_shift_669_ = lean_ctor_get_usize(v_t_665_, 4);
v_tailOff_670_ = lean_ctor_get(v_t_665_, 3);
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_array_get_size(v_tail_667_);
v___x_673_ = lean_nat_dec_lt(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; lean_object* v_fst_675_; 
lean_inc_ref(v_root_666_);
v___x_674_ = l_Lean_PersistentArray_popLeaf___redArg(v_root_666_);
v_fst_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_fst_675_);
if (lean_obj_tag(v_fst_675_) == 0)
{
lean_dec_ref(v___x_674_);
return v_t_665_;
}
else
{
lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_708_; 
lean_inc(v_size_668_);
v_isSharedCheck_708_ = !lean_is_exclusive(v_t_665_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; lean_object* v_unused_710_; lean_object* v_unused_711_; lean_object* v_unused_712_; 
v_unused_709_ = lean_ctor_get(v_t_665_, 3);
lean_dec(v_unused_709_);
v_unused_710_ = lean_ctor_get(v_t_665_, 2);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_t_665_, 1);
lean_dec(v_unused_711_);
v_unused_712_ = lean_ctor_get(v_t_665_, 0);
lean_dec(v_unused_712_);
v___x_677_ = v_t_665_;
v_isShared_678_ = v_isSharedCheck_708_;
goto v_resetjp_676_;
}
else
{
lean_dec(v_t_665_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_708_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_snd_679_; lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_707_; 
v_snd_679_ = lean_ctor_get(v___x_674_, 1);
lean_inc(v_snd_679_);
lean_dec_ref(v___x_674_);
v_val_680_ = lean_ctor_get(v_fst_675_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v_fst_675_);
if (v_isSharedCheck_707_ == 0)
{
v___x_682_ = v_fst_675_;
v_isShared_683_ = v_isSharedCheck_707_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v_fst_675_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_707_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v_last_684_; lean_object* v___x_685_; lean_object* v_newSize_686_; lean_object* v___x_687_; lean_object* v_newTailOff_688_; uint8_t v___y_690_; lean_object* v___x_703_; uint8_t v___x_704_; 
v_last_684_ = lean_array_pop(v_val_680_);
v___x_685_ = lean_unsigned_to_nat(1u);
v_newSize_686_ = lean_nat_sub(v_size_668_, v___x_685_);
lean_dec(v_size_668_);
v___x_687_ = lean_array_get_size(v_last_684_);
v_newTailOff_688_ = lean_nat_sub(v_newSize_686_, v___x_687_);
v___x_703_ = lean_array_get_size(v_snd_679_);
v___x_704_ = lean_nat_dec_eq(v___x_703_, v___x_685_);
if (v___x_704_ == 0)
{
v___y_690_ = v___x_704_;
goto v___jp_689_;
}
else
{
lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_705_ = lean_array_fget_borrowed(v_snd_679_, v___x_671_);
v___x_706_ = l_Lean_PersistentArrayNode_isNode___redArg(v___x_705_);
v___y_690_ = v___x_706_;
goto v___jp_689_;
}
v___jp_689_:
{
if (v___y_690_ == 0)
{
lean_object* v___x_692_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set_tag(v___x_682_, 0);
lean_ctor_set(v___x_682_, 0, v_snd_679_);
v___x_692_ = v___x_682_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_snd_679_);
v___x_692_ = v_reuseFailAlloc_696_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 3, v_newTailOff_688_);
lean_ctor_set(v___x_677_, 2, v_newSize_686_);
lean_ctor_set(v___x_677_, 1, v_last_684_);
lean_ctor_set(v___x_677_, 0, v___x_692_);
v___x_694_ = v___x_677_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_last_684_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_newSize_686_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_newTailOff_688_);
lean_ctor_set_usize(v_reuseFailAlloc_695_, 4, v_shift_669_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
else
{
lean_object* v___x_697_; size_t v___x_698_; size_t v___x_699_; lean_object* v___x_701_; 
lean_del_object(v___x_682_);
v___x_697_ = lean_array_fget(v_snd_679_, v___x_671_);
lean_dec(v_snd_679_);
v___x_698_ = ((size_t)5ULL);
v___x_699_ = lean_usize_sub(v_shift_669_, v___x_698_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 3, v_newTailOff_688_);
lean_ctor_set(v___x_677_, 2, v_newSize_686_);
lean_ctor_set(v___x_677_, 1, v_last_684_);
lean_ctor_set(v___x_677_, 0, v___x_697_);
v___x_701_ = v___x_677_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_last_684_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v_newSize_686_);
lean_ctor_set(v_reuseFailAlloc_702_, 3, v_newTailOff_688_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_ctor_set_usize(v___x_701_, 4, v___x_699_);
return v___x_701_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_722_; 
lean_inc(v_tailOff_670_);
lean_inc(v_size_668_);
lean_inc_ref(v_tail_667_);
lean_inc_ref(v_root_666_);
v_isSharedCheck_722_ = !lean_is_exclusive(v_t_665_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; lean_object* v_unused_724_; lean_object* v_unused_725_; lean_object* v_unused_726_; 
v_unused_723_ = lean_ctor_get(v_t_665_, 3);
lean_dec(v_unused_723_);
v_unused_724_ = lean_ctor_get(v_t_665_, 2);
lean_dec(v_unused_724_);
v_unused_725_ = lean_ctor_get(v_t_665_, 1);
lean_dec(v_unused_725_);
v_unused_726_ = lean_ctor_get(v_t_665_, 0);
lean_dec(v_unused_726_);
v___x_714_ = v_t_665_;
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
else
{
lean_dec(v_t_665_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_722_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_716_ = lean_array_pop(v_tail_667_);
v___x_717_ = lean_unsigned_to_nat(1u);
v___x_718_ = lean_nat_sub(v_size_668_, v___x_717_);
lean_dec(v_size_668_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 2, v___x_718_);
lean_ctor_set(v___x_714_, 1, v___x_716_);
v___x_720_ = v___x_714_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_root_666_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_tailOff_670_);
lean_ctor_set_usize(v_reuseFailAlloc_721_, 4, v_shift_669_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_pop(lean_object* v_00_u03b1_727_, lean_object* v_t_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_PersistentArray_pop___redArg(v_t_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(lean_object* v_inst_730_, lean_object* v_f_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_732_) == 0)
{
lean_object* v_toApplicative_734_; lean_object* v_cs_735_; lean_object* v_toPure_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_toApplicative_734_ = lean_ctor_get(v_inst_730_, 0);
v_cs_735_ = lean_ctor_get(v_x_732_, 0);
lean_inc_ref(v_cs_735_);
lean_dec_ref_known(v_x_732_, 1);
v_toPure_736_ = lean_ctor_get(v_toApplicative_734_, 1);
v___x_737_ = lean_unsigned_to_nat(0u);
v___x_738_ = lean_array_get_size(v_cs_735_);
v___x_739_ = lean_nat_dec_lt(v___x_737_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_inc(v_toPure_736_);
lean_dec_ref(v_cs_735_);
lean_dec(v_f_731_);
lean_dec_ref(v_inst_730_);
v___x_740_ = lean_apply_2(v_toPure_736_, lean_box(0), v_x_733_);
return v___x_740_;
}
else
{
lean_object* v___f_741_; uint8_t v___x_742_; 
lean_inc_ref(v_inst_730_);
v___f_741_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_741_, 0, v_inst_730_);
lean_closure_set(v___f_741_, 1, v_f_731_);
v___x_742_ = lean_nat_dec_le(v___x_738_, v___x_738_);
if (v___x_742_ == 0)
{
if (v___x_739_ == 0)
{
lean_object* v___x_743_; 
lean_inc(v_toPure_736_);
lean_dec_ref(v___f_741_);
lean_dec_ref(v_cs_735_);
lean_dec_ref(v_inst_730_);
v___x_743_ = lean_apply_2(v_toPure_736_, lean_box(0), v_x_733_);
return v___x_743_;
}
else
{
size_t v___x_744_; size_t v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((size_t)0ULL);
v___x_745_ = lean_usize_of_nat(v___x_738_);
v___x_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_730_, v___f_741_, v_cs_735_, v___x_744_, v___x_745_, v_x_733_);
return v___x_746_;
}
}
else
{
size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = ((size_t)0ULL);
v___x_748_ = lean_usize_of_nat(v___x_738_);
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_730_, v___f_741_, v_cs_735_, v___x_747_, v___x_748_, v_x_733_);
return v___x_749_;
}
}
}
else
{
lean_object* v_toApplicative_750_; lean_object* v_vs_751_; lean_object* v_toPure_752_; lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v_toApplicative_750_ = lean_ctor_get(v_inst_730_, 0);
v_vs_751_ = lean_ctor_get(v_x_732_, 0);
lean_inc_ref(v_vs_751_);
lean_dec_ref_known(v_x_732_, 1);
v_toPure_752_ = lean_ctor_get(v_toApplicative_750_, 1);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_array_get_size(v_vs_751_);
v___x_755_ = lean_nat_dec_lt(v___x_753_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; 
lean_inc(v_toPure_752_);
lean_dec_ref(v_vs_751_);
lean_dec(v_f_731_);
lean_dec_ref(v_inst_730_);
v___x_756_ = lean_apply_2(v_toPure_752_, lean_box(0), v_x_733_);
return v___x_756_;
}
else
{
uint8_t v___x_757_; 
v___x_757_ = lean_nat_dec_le(v___x_754_, v___x_754_);
if (v___x_757_ == 0)
{
if (v___x_755_ == 0)
{
lean_object* v___x_758_; 
lean_inc(v_toPure_752_);
lean_dec_ref(v_vs_751_);
lean_dec(v_f_731_);
lean_dec_ref(v_inst_730_);
v___x_758_ = lean_apply_2(v_toPure_752_, lean_box(0), v_x_733_);
return v___x_758_;
}
else
{
size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_754_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_730_, v_f_731_, v_vs_751_, v___x_759_, v___x_760_, v_x_733_);
return v___x_761_;
}
}
else
{
size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
v___x_762_ = ((size_t)0ULL);
v___x_763_ = lean_usize_of_nat(v___x_754_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_730_, v_f_731_, v_vs_751_, v___x_762_, v___x_763_, v_x_733_);
return v___x_764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0(lean_object* v_inst_765_, lean_object* v_f_766_, lean_object* v_b_767_, lean_object* v_c_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_765_, v_f_766_, v_c_768_, v_b_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux(lean_object* v_00_u03b1_770_, lean_object* v_m_771_, lean_object* v_inst_772_, lean_object* v_00_u03b2_773_, lean_object* v_f_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_772_, v_f_774_, v_x_775_, v_x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(lean_object* v_toApplicative_778_, lean_object* v_j_779_, lean_object* v_cs_780_, lean_object* v_inst_781_, lean_object* v___f_782_, lean_object* v_b_783_){
_start:
{
lean_object* v_toPure_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_toPure_784_ = lean_ctor_get(v_toApplicative_778_, 1);
lean_inc(v_toPure_784_);
lean_dec_ref(v_toApplicative_778_);
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = lean_nat_add(v_j_779_, v___x_785_);
v___x_787_ = lean_array_get_size(v_cs_780_);
v___x_788_ = lean_nat_dec_lt(v___x_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_dec(v___x_786_);
lean_dec(v___f_782_);
lean_dec_ref(v_inst_781_);
lean_dec_ref(v_cs_780_);
v___x_789_ = lean_apply_2(v_toPure_784_, lean_box(0), v_b_783_);
return v___x_789_;
}
else
{
uint8_t v___x_790_; 
v___x_790_ = lean_nat_dec_le(v___x_787_, v___x_787_);
if (v___x_790_ == 0)
{
if (v___x_788_ == 0)
{
lean_object* v___x_791_; 
lean_dec(v___x_786_);
lean_dec(v___f_782_);
lean_dec_ref(v_inst_781_);
lean_dec_ref(v_cs_780_);
v___x_791_ = lean_apply_2(v_toPure_784_, lean_box(0), v_b_783_);
return v___x_791_;
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; 
lean_dec(v_toPure_784_);
v___x_792_ = lean_usize_of_nat(v___x_786_);
lean_dec(v___x_786_);
v___x_793_ = lean_usize_of_nat(v___x_787_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_781_, v___f_782_, v_cs_780_, v___x_792_, v___x_793_, v_b_783_);
return v___x_794_;
}
}
else
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
lean_dec(v_toPure_784_);
v___x_795_ = lean_usize_of_nat(v___x_786_);
lean_dec(v___x_786_);
v___x_796_ = lean_usize_of_nat(v___x_787_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_781_, v___f_782_, v_cs_780_, v___x_795_, v___x_796_, v_b_783_);
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_798_, lean_object* v_j_799_, lean_object* v_cs_800_, lean_object* v_inst_801_, lean_object* v___f_802_, lean_object* v_b_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1(v_toApplicative_798_, v_j_799_, v_cs_800_, v_inst_801_, v___f_802_, v_b_803_);
lean_dec(v_j_799_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(lean_object* v_inst_805_, lean_object* v_f_806_, lean_object* v_x_807_, size_t v_x_808_, size_t v_x_809_, lean_object* v_x_810_){
_start:
{
if (lean_obj_tag(v_x_807_) == 0)
{
lean_object* v_toApplicative_811_; lean_object* v_toBind_812_; lean_object* v_cs_813_; lean_object* v___f_814_; lean_object* v___x_815_; size_t v___x_816_; lean_object* v_j_817_; lean_object* v___f_818_; lean_object* v___x_819_; size_t v___x_820_; size_t v___x_821_; size_t v___x_822_; size_t v___x_823_; size_t v___x_824_; size_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_toApplicative_811_ = lean_ctor_get(v_inst_805_, 0);
v_toBind_812_ = lean_ctor_get(v_inst_805_, 1);
lean_inc(v_toBind_812_);
v_cs_813_ = lean_ctor_get(v_x_807_, 0);
lean_inc_ref_n(v_cs_813_, 2);
lean_dec_ref_known(v_x_807_, 1);
lean_inc(v_f_806_);
lean_inc_ref_n(v_inst_805_, 2);
v___f_814_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_814_, 0, v_inst_805_);
lean_closure_set(v___f_814_, 1, v_f_806_);
v___x_815_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_816_ = lean_usize_shift_right(v_x_808_, v_x_809_);
v_j_817_ = lean_usize_to_nat(v___x_816_);
lean_inc(v_j_817_);
lean_inc_ref(v_toApplicative_811_);
v___f_818_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_818_, 0, v_toApplicative_811_);
lean_closure_set(v___f_818_, 1, v_j_817_);
lean_closure_set(v___f_818_, 2, v_cs_813_);
lean_closure_set(v___f_818_, 3, v_inst_805_);
lean_closure_set(v___f_818_, 4, v___f_814_);
v___x_819_ = lean_array_get(v___x_815_, v_cs_813_, v_j_817_);
lean_dec(v_j_817_);
lean_dec_ref(v_cs_813_);
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_shift_left(v___x_820_, v_x_809_);
v___x_822_ = lean_usize_sub(v___x_821_, v___x_820_);
v___x_823_ = lean_usize_land(v_x_808_, v___x_822_);
v___x_824_ = ((size_t)5ULL);
v___x_825_ = lean_usize_sub(v_x_809_, v___x_824_);
v___x_826_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_805_, v_f_806_, v___x_819_, v___x_823_, v___x_825_, v_x_810_);
v___x_827_ = lean_apply_4(v_toBind_812_, lean_box(0), lean_box(0), v___x_826_, v___f_818_);
return v___x_827_;
}
else
{
lean_object* v_toApplicative_828_; lean_object* v_vs_829_; lean_object* v_toPure_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_toApplicative_828_ = lean_ctor_get(v_inst_805_, 0);
v_vs_829_ = lean_ctor_get(v_x_807_, 0);
lean_inc_ref(v_vs_829_);
lean_dec_ref_known(v_x_807_, 1);
v_toPure_830_ = lean_ctor_get(v_toApplicative_828_, 1);
v___x_831_ = lean_usize_to_nat(v_x_808_);
v___x_832_ = lean_array_get_size(v_vs_829_);
v___x_833_ = lean_nat_dec_lt(v___x_831_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_inc(v_toPure_830_);
lean_dec(v___x_831_);
lean_dec_ref(v_vs_829_);
lean_dec(v_f_806_);
lean_dec_ref(v_inst_805_);
v___x_834_ = lean_apply_2(v_toPure_830_, lean_box(0), v_x_810_);
return v___x_834_;
}
else
{
uint8_t v___x_835_; 
v___x_835_ = lean_nat_dec_le(v___x_832_, v___x_832_);
if (v___x_835_ == 0)
{
if (v___x_833_ == 0)
{
lean_object* v___x_836_; 
lean_inc(v_toPure_830_);
lean_dec(v___x_831_);
lean_dec_ref(v_vs_829_);
lean_dec(v_f_806_);
lean_dec_ref(v_inst_805_);
v___x_836_ = lean_apply_2(v_toPure_830_, lean_box(0), v_x_810_);
return v___x_836_;
}
else
{
size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; 
v___x_837_ = lean_usize_of_nat(v___x_831_);
lean_dec(v___x_831_);
v___x_838_ = lean_usize_of_nat(v___x_832_);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_805_, v_f_806_, v_vs_829_, v___x_837_, v___x_838_, v_x_810_);
return v___x_839_;
}
}
else
{
size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; 
v___x_840_ = lean_usize_of_nat(v___x_831_);
lean_dec(v___x_831_);
v___x_841_ = lean_usize_of_nat(v___x_832_);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_805_, v_f_806_, v_vs_829_, v___x_840_, v___x_841_, v_x_810_);
return v___x_842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg___boxed(lean_object* v_inst_843_, lean_object* v_f_844_, lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
size_t v_x_206__boxed_849_; size_t v_x_207__boxed_850_; lean_object* v_res_851_; 
v_x_206__boxed_849_ = lean_unbox_usize(v_x_846_);
lean_dec(v_x_846_);
v_x_207__boxed_850_ = lean_unbox_usize(v_x_847_);
lean_dec(v_x_847_);
v_res_851_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_843_, v_f_844_, v_x_845_, v_x_206__boxed_849_, v_x_207__boxed_850_, v_x_848_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(lean_object* v_00_u03b1_852_, lean_object* v_m_853_, lean_object* v_inst_854_, lean_object* v_00_u03b2_855_, lean_object* v_f_856_, lean_object* v_x_857_, size_t v_x_858_, size_t v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_854_, v_f_856_, v_x_857_, v_x_858_, v_x_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___boxed(lean_object* v_00_u03b1_862_, lean_object* v_m_863_, lean_object* v_inst_864_, lean_object* v_00_u03b2_865_, lean_object* v_f_866_, lean_object* v_x_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
size_t v_x_275__boxed_871_; size_t v_x_276__boxed_872_; lean_object* v_res_873_; 
v_x_275__boxed_871_ = lean_unbox_usize(v_x_868_);
lean_dec(v_x_868_);
v_x_276__boxed_872_ = lean_unbox_usize(v_x_869_);
lean_dec(v_x_869_);
v_res_873_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux(v_00_u03b1_862_, v_m_863_, v_inst_864_, v_00_u03b2_865_, v_f_866_, v_x_867_, v_x_275__boxed_871_, v_x_276__boxed_872_, v_x_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0(lean_object* v_toApplicative_874_, lean_object* v_tail_875_, lean_object* v___x_876_, lean_object* v_inst_877_, lean_object* v_f_878_, lean_object* v_b_879_){
_start:
{
lean_object* v_toPure_880_; lean_object* v___x_881_; uint8_t v___x_882_; 
v_toPure_880_ = lean_ctor_get(v_toApplicative_874_, 1);
lean_inc(v_toPure_880_);
lean_dec_ref(v_toApplicative_874_);
v___x_881_ = lean_array_get_size(v_tail_875_);
v___x_882_ = lean_nat_dec_lt(v___x_876_, v___x_881_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
lean_dec(v_f_878_);
lean_dec_ref(v_inst_877_);
lean_dec_ref(v_tail_875_);
v___x_883_ = lean_apply_2(v_toPure_880_, lean_box(0), v_b_879_);
return v___x_883_;
}
else
{
uint8_t v___x_884_; 
v___x_884_ = lean_nat_dec_le(v___x_881_, v___x_881_);
if (v___x_884_ == 0)
{
if (v___x_882_ == 0)
{
lean_object* v___x_885_; 
lean_dec(v_f_878_);
lean_dec_ref(v_inst_877_);
lean_dec_ref(v_tail_875_);
v___x_885_ = lean_apply_2(v_toPure_880_, lean_box(0), v_b_879_);
return v___x_885_;
}
else
{
size_t v___x_886_; size_t v___x_887_; lean_object* v___x_888_; 
lean_dec(v_toPure_880_);
v___x_886_ = ((size_t)0ULL);
v___x_887_ = lean_usize_of_nat(v___x_881_);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_877_, v_f_878_, v_tail_875_, v___x_886_, v___x_887_, v_b_879_);
return v___x_888_;
}
}
else
{
size_t v___x_889_; size_t v___x_890_; lean_object* v___x_891_; 
lean_dec(v_toPure_880_);
v___x_889_ = ((size_t)0ULL);
v___x_890_ = lean_usize_of_nat(v___x_881_);
v___x_891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_877_, v_f_878_, v_tail_875_, v___x_889_, v___x_890_, v_b_879_);
return v___x_891_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed(lean_object* v_toApplicative_892_, lean_object* v_tail_893_, lean_object* v___x_894_, lean_object* v_inst_895_, lean_object* v_f_896_, lean_object* v_b_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_PersistentArray_foldlM___redArg___lam__0(v_toApplicative_892_, v_tail_893_, v___x_894_, v_inst_895_, v_f_896_, v_b_897_);
lean_dec(v___x_894_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg(lean_object* v_inst_899_, lean_object* v_t_900_, lean_object* v_f_901_, lean_object* v_init_902_, lean_object* v_start_903_){
_start:
{
lean_object* v_toApplicative_904_; lean_object* v_toBind_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
v_toApplicative_904_ = lean_ctor_get(v_inst_899_, 0);
v_toBind_905_ = lean_ctor_get(v_inst_899_, 1);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_nat_dec_eq(v_start_903_, v___x_906_);
if (v___x_907_ == 0)
{
lean_object* v_root_908_; lean_object* v_tail_909_; size_t v_shift_910_; lean_object* v_tailOff_911_; uint8_t v___x_912_; 
v_root_908_ = lean_ctor_get(v_t_900_, 0);
lean_inc_ref(v_root_908_);
v_tail_909_ = lean_ctor_get(v_t_900_, 1);
lean_inc_ref(v_tail_909_);
v_shift_910_ = lean_ctor_get_usize(v_t_900_, 4);
v_tailOff_911_ = lean_ctor_get(v_t_900_, 3);
lean_inc(v_tailOff_911_);
lean_dec_ref(v_t_900_);
v___x_912_ = lean_nat_dec_le(v_tailOff_911_, v_start_903_);
if (v___x_912_ == 0)
{
lean_object* v___f_913_; size_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
lean_inc(v_toBind_905_);
lean_dec(v_tailOff_911_);
lean_inc(v_f_901_);
lean_inc_ref(v_inst_899_);
lean_inc_ref(v_toApplicative_904_);
v___f_913_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_913_, 0, v_toApplicative_904_);
lean_closure_set(v___f_913_, 1, v_tail_909_);
lean_closure_set(v___f_913_, 2, v___x_906_);
lean_closure_set(v___f_913_, 3, v_inst_899_);
lean_closure_set(v___f_913_, 4, v_f_901_);
v___x_914_ = lean_usize_of_nat(v_start_903_);
v___x_915_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___redArg(v_inst_899_, v_f_901_, v_root_908_, v___x_914_, v_shift_910_, v_init_902_);
v___x_916_ = lean_apply_4(v_toBind_905_, lean_box(0), lean_box(0), v___x_915_, v___f_913_);
return v___x_916_;
}
else
{
lean_object* v_toPure_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
lean_dec_ref(v_root_908_);
v_toPure_917_ = lean_ctor_get(v_toApplicative_904_, 1);
v___x_918_ = lean_nat_sub(v_start_903_, v_tailOff_911_);
lean_dec(v_tailOff_911_);
v___x_919_ = lean_array_get_size(v_tail_909_);
v___x_920_ = lean_nat_dec_lt(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
lean_inc(v_toPure_917_);
lean_dec(v___x_918_);
lean_dec_ref(v_tail_909_);
lean_dec(v_f_901_);
lean_dec_ref(v_inst_899_);
v___x_921_ = lean_apply_2(v_toPure_917_, lean_box(0), v_init_902_);
return v___x_921_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = lean_nat_dec_le(v___x_919_, v___x_919_);
if (v___x_922_ == 0)
{
if (v___x_920_ == 0)
{
lean_object* v___x_923_; 
lean_inc(v_toPure_917_);
lean_dec(v___x_918_);
lean_dec_ref(v_tail_909_);
lean_dec(v_f_901_);
lean_dec_ref(v_inst_899_);
v___x_923_ = lean_apply_2(v_toPure_917_, lean_box(0), v_init_902_);
return v___x_923_;
}
else
{
size_t v___x_924_; size_t v___x_925_; lean_object* v___x_926_; 
v___x_924_ = lean_usize_of_nat(v___x_918_);
lean_dec(v___x_918_);
v___x_925_ = lean_usize_of_nat(v___x_919_);
v___x_926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_899_, v_f_901_, v_tail_909_, v___x_924_, v___x_925_, v_init_902_);
return v___x_926_;
}
}
else
{
size_t v___x_927_; size_t v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_usize_of_nat(v___x_918_);
lean_dec(v___x_918_);
v___x_928_ = lean_usize_of_nat(v___x_919_);
v___x_929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_899_, v_f_901_, v_tail_909_, v___x_927_, v___x_928_, v_init_902_);
return v___x_929_;
}
}
}
}
else
{
lean_object* v_root_930_; lean_object* v_tail_931_; lean_object* v___f_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_inc(v_toBind_905_);
v_root_930_ = lean_ctor_get(v_t_900_, 0);
lean_inc_ref(v_root_930_);
v_tail_931_ = lean_ctor_get(v_t_900_, 1);
lean_inc_ref(v_tail_931_);
lean_dec_ref(v_t_900_);
lean_inc(v_f_901_);
lean_inc_ref(v_inst_899_);
lean_inc_ref(v_toApplicative_904_);
v___f_932_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldlM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_932_, 0, v_toApplicative_904_);
lean_closure_set(v___f_932_, 1, v_tail_931_);
lean_closure_set(v___f_932_, 2, v___x_906_);
lean_closure_set(v___f_932_, 3, v_inst_899_);
lean_closure_set(v___f_932_, 4, v_f_901_);
v___x_933_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___redArg(v_inst_899_, v_f_901_, v_root_930_, v_init_902_);
v___x_934_ = lean_apply_4(v_toBind_905_, lean_box(0), lean_box(0), v___x_933_, v___f_932_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___redArg___boxed(lean_object* v_inst_935_, lean_object* v_t_936_, lean_object* v_f_937_, lean_object* v_init_938_, lean_object* v_start_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_935_, v_t_936_, v_f_937_, v_init_938_, v_start_939_);
lean_dec(v_start_939_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM(lean_object* v_00_u03b1_941_, lean_object* v_m_942_, lean_object* v_inst_943_, lean_object* v_00_u03b2_944_, lean_object* v_t_945_, lean_object* v_f_946_, lean_object* v_init_947_, lean_object* v_start_948_){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_PersistentArray_foldlM___redArg(v_inst_943_, v_t_945_, v_f_946_, v_init_947_, v_start_948_);
return v___x_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___boxed(lean_object* v_00_u03b1_950_, lean_object* v_m_951_, lean_object* v_inst_952_, lean_object* v_00_u03b2_953_, lean_object* v_t_954_, lean_object* v_f_955_, lean_object* v_init_956_, lean_object* v_start_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_PersistentArray_foldlM(v_00_u03b1_950_, v_m_951_, v_inst_952_, v_00_u03b2_953_, v_t_954_, v_f_955_, v_init_956_, v_start_957_);
lean_dec(v_start_957_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(lean_object* v_inst_959_, lean_object* v_f_960_, lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
if (lean_obj_tag(v_x_961_) == 0)
{
lean_object* v_toApplicative_963_; lean_object* v_cs_964_; lean_object* v_toPure_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_toApplicative_963_ = lean_ctor_get(v_inst_959_, 0);
v_cs_964_ = lean_ctor_get(v_x_961_, 0);
lean_inc_ref(v_cs_964_);
lean_dec_ref_known(v_x_961_, 1);
v_toPure_965_ = lean_ctor_get(v_toApplicative_963_, 1);
v___x_966_ = lean_array_get_size(v_cs_964_);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_nat_dec_lt(v___x_967_, v___x_966_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
lean_inc(v_toPure_965_);
lean_dec_ref(v_cs_964_);
lean_dec(v_f_960_);
lean_dec_ref(v_inst_959_);
v___x_969_ = lean_apply_2(v_toPure_965_, lean_box(0), v_x_962_);
return v___x_969_;
}
else
{
lean_object* v___f_970_; size_t v___x_971_; size_t v___x_972_; lean_object* v___x_973_; 
lean_inc_ref(v_inst_959_);
v___f_970_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_970_, 0, v_inst_959_);
lean_closure_set(v___f_970_, 1, v_f_960_);
v___x_971_ = lean_usize_of_nat(v___x_966_);
v___x_972_ = ((size_t)0ULL);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_959_, v___f_970_, v_cs_964_, v___x_971_, v___x_972_, v_x_962_);
return v___x_973_;
}
}
else
{
lean_object* v_toApplicative_974_; lean_object* v_vs_975_; lean_object* v_toPure_976_; lean_object* v___x_977_; lean_object* v___x_978_; uint8_t v___x_979_; 
v_toApplicative_974_ = lean_ctor_get(v_inst_959_, 0);
v_vs_975_ = lean_ctor_get(v_x_961_, 0);
lean_inc_ref(v_vs_975_);
lean_dec_ref_known(v_x_961_, 1);
v_toPure_976_ = lean_ctor_get(v_toApplicative_974_, 1);
v___x_977_ = lean_array_get_size(v_vs_975_);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_nat_dec_lt(v___x_978_, v___x_977_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
lean_inc(v_toPure_976_);
lean_dec_ref(v_vs_975_);
lean_dec(v_f_960_);
lean_dec_ref(v_inst_959_);
v___x_980_ = lean_apply_2(v_toPure_976_, lean_box(0), v_x_962_);
return v___x_980_;
}
else
{
size_t v___x_981_; size_t v___x_982_; lean_object* v___x_983_; 
v___x_981_ = lean_usize_of_nat(v___x_977_);
v___x_982_ = ((size_t)0ULL);
v___x_983_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_959_, v_f_960_, v_vs_975_, v___x_981_, v___x_982_, v_x_962_);
return v___x_983_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg___lam__0(lean_object* v_inst_984_, lean_object* v_f_985_, lean_object* v_c_986_, lean_object* v_b_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_984_, v_f_985_, v_c_986_, v_b_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux(lean_object* v_00_u03b1_989_, lean_object* v_m_990_, lean_object* v_00_u03b2_991_, lean_object* v_inst_992_, lean_object* v_f_993_, lean_object* v_x_994_, lean_object* v_x_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_992_, v_f_993_, v_x_994_, v_x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg___lam__0(lean_object* v_inst_997_, lean_object* v_f_998_, lean_object* v_root_999_, lean_object* v_____do__lift_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldrMAux___redArg(v_inst_997_, v_f_998_, v_root_999_, v_____do__lift_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM___redArg(lean_object* v_inst_1002_, lean_object* v_t_1003_, lean_object* v_f_1004_, lean_object* v_init_1005_){
_start:
{
lean_object* v_toApplicative_1006_; lean_object* v_toBind_1007_; lean_object* v_root_1008_; lean_object* v_tail_1009_; lean_object* v_toPure_1010_; lean_object* v___f_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_toApplicative_1006_ = lean_ctor_get(v_inst_1002_, 0);
v_toBind_1007_ = lean_ctor_get(v_inst_1002_, 1);
lean_inc(v_toBind_1007_);
v_root_1008_ = lean_ctor_get(v_t_1003_, 0);
lean_inc_ref(v_root_1008_);
v_tail_1009_ = lean_ctor_get(v_t_1003_, 1);
lean_inc_ref(v_tail_1009_);
lean_dec_ref(v_t_1003_);
v_toPure_1010_ = lean_ctor_get(v_toApplicative_1006_, 1);
lean_inc(v_f_1004_);
lean_inc_ref(v_inst_1002_);
v___f_1011_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1011_, 0, v_inst_1002_);
lean_closure_set(v___f_1011_, 1, v_f_1004_);
lean_closure_set(v___f_1011_, 2, v_root_1008_);
v___x_1012_ = lean_array_get_size(v_tail_1009_);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_nat_dec_lt(v___x_1013_, v___x_1012_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_inc(v_toPure_1010_);
lean_dec_ref(v_tail_1009_);
lean_dec(v_f_1004_);
lean_dec_ref(v_inst_1002_);
v___x_1015_ = lean_apply_2(v_toPure_1010_, lean_box(0), v_init_1005_);
v___x_1016_ = lean_apply_4(v_toBind_1007_, lean_box(0), lean_box(0), v___x_1015_, v___f_1011_);
return v___x_1016_;
}
else
{
size_t v___x_1017_; size_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1017_ = lean_usize_of_nat(v___x_1012_);
v___x_1018_ = ((size_t)0ULL);
v___x_1019_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1002_, v_f_1004_, v_tail_1009_, v___x_1017_, v___x_1018_, v_init_1005_);
v___x_1020_ = lean_apply_4(v_toBind_1007_, lean_box(0), lean_box(0), v___x_1019_, v___f_1011_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldrM(lean_object* v_00_u03b1_1021_, lean_object* v_m_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_inst_1024_, lean_object* v_t_1025_, lean_object* v_f_1026_, lean_object* v_init_1027_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_PersistentArray_foldrM___redArg(v_inst_1024_, v_t_1025_, v_f_1026_, v_init_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__0(lean_object* v_toPure_1029_, lean_object* v_____s_1030_){
_start:
{
lean_object* v_fst_1031_; 
v_fst_1031_ = lean_ctor_get(v_____s_1030_, 0);
if (lean_obj_tag(v_fst_1031_) == 0)
{
lean_object* v_snd_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_snd_1032_ = lean_ctor_get(v_____s_1030_, 1);
lean_inc(v_snd_1032_);
lean_dec_ref(v_____s_1030_);
v___x_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1033_, 0, v_snd_1032_);
v___x_1034_ = lean_apply_2(v_toPure_1029_, lean_box(0), v___x_1033_);
return v___x_1034_;
}
else
{
lean_object* v_val_1035_; lean_object* v___x_1036_; 
lean_inc_ref(v_fst_1031_);
lean_dec_ref(v_____s_1030_);
v_val_1035_ = lean_ctor_get(v_fst_1031_, 0);
lean_inc(v_val_1035_);
lean_dec_ref_known(v_fst_1031_, 1);
v___x_1036_ = lean_apply_2(v_toPure_1029_, lean_box(0), v_val_1035_);
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__1(lean_object* v_snd_1037_, lean_object* v_toPure_1038_, lean_object* v___x_1039_, lean_object* v_____do__lift_1040_){
_start:
{
if (lean_obj_tag(v_____do__lift_1040_) == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v___x_1039_);
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_____do__lift_1040_);
v___x_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v_snd_1037_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
v___x_1044_ = lean_apply_2(v_toPure_1038_, lean_box(0), v___x_1043_);
return v___x_1044_;
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_snd_1037_);
v_a_1045_ = lean_ctor_get(v_____do__lift_1040_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_____do__lift_1040_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1047_ = v_____do__lift_1040_;
v_isShared_1048_ = v_isSharedCheck_1054_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v_____do__lift_1040_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1054_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1039_);
lean_ctor_set(v___x_1049_, 1, v_a_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1049_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_apply_2(v_toPure_1038_, lean_box(0), v___x_1051_);
return v___x_1052_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__5(lean_object* v_toPure_1055_, lean_object* v___x_1056_, lean_object* v_f_1057_, lean_object* v_toBind_1058_, lean_object* v_a_1059_, lean_object* v_x_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_snd_1062_; lean_object* v___f_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_snd_1062_ = lean_ctor_get(v___y_1061_, 1);
lean_inc_n(v_snd_1062_, 2);
lean_dec_ref(v___y_1061_);
v___f_1063_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1063_, 0, v_snd_1062_);
lean_closure_set(v___f_1063_, 1, v_toPure_1055_);
lean_closure_set(v___f_1063_, 2, v___x_1056_);
v___x_1064_ = lean_apply_2(v_f_1057_, v_a_1059_, v_snd_1062_);
v___x_1065_ = lean_apply_4(v_toBind_1058_, lean_box(0), lean_box(0), v___x_1064_, v___f_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed(lean_object* v_toPure_1066_, lean_object* v___x_1067_, lean_object* v_inst_1068_, lean_object* v_f_1069_, lean_object* v_toBind_1070_, lean_object* v_a_1071_, lean_object* v_x_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_PersistentArray_forInAux___redArg___lam__2(v_toPure_1066_, v___x_1067_, v_inst_1068_, v_f_1069_, v_toBind_1070_, v_a_1071_, v_x_1072_, v___y_1073_);
lean_dec_ref(v_a_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg(lean_object* v_inst_1075_, lean_object* v_f_1076_, lean_object* v_n_1077_, lean_object* v_b_1078_){
_start:
{
if (lean_obj_tag(v_n_1077_) == 0)
{
lean_object* v_toApplicative_1079_; lean_object* v_toBind_1080_; lean_object* v_toPure_1081_; lean_object* v_cs_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; size_t v_sz_1087_; size_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v_toApplicative_1079_ = lean_ctor_get(v_inst_1075_, 0);
v_toBind_1080_ = lean_ctor_get(v_inst_1075_, 1);
lean_inc_n(v_toBind_1080_, 2);
v_toPure_1081_ = lean_ctor_get(v_toApplicative_1079_, 1);
v_cs_1082_ = lean_ctor_get(v_n_1077_, 0);
lean_inc_n(v_toPure_1081_, 2);
v___f_1083_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1083_, 0, v_toPure_1081_);
v___x_1084_ = lean_box(0);
lean_inc_ref(v_inst_1075_);
v___f_1085_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__2___boxed), 8, 5);
lean_closure_set(v___f_1085_, 0, v_toPure_1081_);
lean_closure_set(v___f_1085_, 1, v___x_1084_);
lean_closure_set(v___f_1085_, 2, v_inst_1075_);
lean_closure_set(v___f_1085_, 3, v_f_1076_);
lean_closure_set(v___f_1085_, 4, v_toBind_1080_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v_b_1078_);
v_sz_1087_ = lean_array_size(v_cs_1082_);
v___x_1088_ = ((size_t)0ULL);
lean_inc_ref(v_cs_1082_);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1075_, v_cs_1082_, v___f_1085_, v_sz_1087_, v___x_1088_, v___x_1086_);
v___x_1090_ = lean_apply_4(v_toBind_1080_, lean_box(0), lean_box(0), v___x_1089_, v___f_1083_);
return v___x_1090_;
}
else
{
lean_object* v_toApplicative_1091_; lean_object* v_toBind_1092_; lean_object* v_toPure_1093_; lean_object* v_vs_1094_; lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___f_1097_; lean_object* v___x_1098_; size_t v_sz_1099_; size_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_toApplicative_1091_ = lean_ctor_get(v_inst_1075_, 0);
v_toBind_1092_ = lean_ctor_get(v_inst_1075_, 1);
lean_inc_n(v_toBind_1092_, 2);
v_toPure_1093_ = lean_ctor_get(v_toApplicative_1091_, 1);
v_vs_1094_ = lean_ctor_get(v_n_1077_, 0);
lean_inc_n(v_toPure_1093_, 2);
v___f_1095_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1095_, 0, v_toPure_1093_);
v___x_1096_ = lean_box(0);
v___f_1097_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__5), 7, 4);
lean_closure_set(v___f_1097_, 0, v_toPure_1093_);
lean_closure_set(v___f_1097_, 1, v___x_1096_);
lean_closure_set(v___f_1097_, 2, v_f_1076_);
lean_closure_set(v___f_1097_, 3, v_toBind_1092_);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v_b_1078_);
v_sz_1099_ = lean_array_size(v_vs_1094_);
v___x_1100_ = ((size_t)0ULL);
lean_inc_ref(v_vs_1094_);
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1075_, v_vs_1094_, v___f_1097_, v_sz_1099_, v___x_1100_, v___x_1098_);
v___x_1102_ = lean_apply_4(v_toBind_1092_, lean_box(0), lean_box(0), v___x_1101_, v___f_1095_);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___lam__2(lean_object* v_toPure_1103_, lean_object* v___x_1104_, lean_object* v_inst_1105_, lean_object* v_f_1106_, lean_object* v_toBind_1107_, lean_object* v_a_1108_, lean_object* v_x_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_snd_1111_; lean_object* v___f_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v_snd_1111_ = lean_ctor_get(v___y_1110_, 1);
lean_inc_n(v_snd_1111_, 2);
lean_dec_ref(v___y_1110_);
v___f_1112_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forInAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1112_, 0, v_snd_1111_);
lean_closure_set(v___f_1112_, 1, v_toPure_1103_);
lean_closure_set(v___f_1112_, 2, v___x_1104_);
v___x_1113_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1105_, v_f_1106_, v_a_1108_, v_snd_1111_);
v___x_1114_ = lean_apply_4(v_toBind_1107_, lean_box(0), lean_box(0), v___x_1113_, v___f_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___redArg___boxed(lean_object* v_inst_1115_, lean_object* v_f_1116_, lean_object* v_n_1117_, lean_object* v_b_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1115_, v_f_1116_, v_n_1117_, v_b_1118_);
lean_dec_ref(v_n_1117_);
return v_res_1119_;
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
lean_dec_ref(v_n_1135_);
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
lean_dec_ref_known(v_fst_1140_, 1);
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
lean_dec_ref_known(v_____do__lift_1187_, 1);
v___x_1189_ = lean_apply_2(v_toPure_1181_, lean_box(0), v_a_1188_);
return v___x_1189_;
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; size_t v_sz_1194_; size_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v_a_1190_ = lean_ctor_get(v_____do__lift_1187_, 0);
lean_inc(v_a_1190_);
lean_dec_ref_known(v_____do__lift_1187_, 1);
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
v_tail_1205_ = lean_ctor_get(v_t_1199_, 1);
v_toPure_1206_ = lean_ctor_get(v_toApplicative_1202_, 1);
lean_inc_n(v_toPure_1206_, 2);
lean_inc(v_f_1201_);
lean_inc_ref(v_inst_1198_);
v___x_1207_ = l_Lean_PersistentArray_forInAux___redArg(v_inst_1198_, v_f_1201_, v_root_1204_, v_init_1200_);
v___f_1208_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1208_, 0, v_toPure_1206_);
lean_inc_ref(v_tail_1205_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___redArg___boxed(lean_object* v_inst_1211_, lean_object* v_t_1212_, lean_object* v_init_1213_, lean_object* v_f_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1211_, v_t_1212_, v_init_1213_, v_f_1214_);
lean_dec_ref(v_t_1212_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn(lean_object* v_00_u03b1_1216_, lean_object* v_m_1217_, lean_object* v_inst_1218_, lean_object* v_00_u03b2_1219_, lean_object* v_t_1220_, lean_object* v_init_1221_, lean_object* v_f_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = l_Lean_PersistentArray_forIn___redArg(v_inst_1218_, v_t_1220_, v_init_1221_, v_f_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___boxed(lean_object* v_00_u03b1_1224_, lean_object* v_m_1225_, lean_object* v_inst_1226_, lean_object* v_00_u03b2_1227_, lean_object* v_t_1228_, lean_object* v_init_1229_, lean_object* v_f_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_PersistentArray_forIn(v_00_u03b1_1224_, v_m_1225_, v_inst_1226_, v_00_u03b2_1227_, v_t_1228_, v_init_1229_, v_f_1230_);
lean_dec_ref(v_t_1228_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad___redArg(lean_object* v_inst_1232_){
_start:
{
lean_object* v___x_1233_; 
v___x_1233_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1233_, 0, lean_box(0));
lean_closure_set(v___x_1233_, 1, lean_box(0));
lean_closure_set(v___x_1233_, 2, v_inst_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instForInOfMonad(lean_object* v_00_u03b1_1234_, lean_object* v_m_1235_, lean_object* v_inst_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forIn___boxed), 7, 3);
lean_closure_set(v___x_1237_, 0, lean_box(0));
lean_closure_set(v___x_1237_, 1, lean_box(0));
lean_closure_set(v___x_1237_, 2, v_inst_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__0(lean_object* v_toPure_1238_, lean_object* v_____s_1239_){
_start:
{
lean_object* v_fst_1240_; 
v_fst_1240_ = lean_ctor_get(v_____s_1239_, 0);
lean_inc(v_fst_1240_);
lean_dec_ref(v_____s_1239_);
if (lean_obj_tag(v_fst_1240_) == 0)
{
lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1241_ = lean_box(0);
v___x_1242_ = lean_apply_2(v_toPure_1238_, lean_box(0), v___x_1241_);
return v___x_1242_;
}
else
{
lean_object* v_val_1243_; lean_object* v___x_1244_; 
v_val_1243_ = lean_ctor_get(v_fst_1240_, 0);
lean_inc(v_val_1243_);
lean_dec_ref_known(v_fst_1240_, 1);
v___x_1244_ = lean_apply_2(v_toPure_1238_, lean_box(0), v_val_1243_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__1(lean_object* v___x_1245_, lean_object* v_toPure_1246_, lean_object* v___x_1247_, lean_object* v_____do__lift_1248_){
_start:
{
if (lean_obj_tag(v_____do__lift_1248_) == 1)
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec_ref(v___x_1247_);
v___x_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_____do__lift_1248_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1245_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
v___x_1252_ = lean_apply_2(v_toPure_1246_, lean_box(0), v___x_1251_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec(v_____do__lift_1248_);
v___x_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1253_, 0, v___x_1247_);
v___x_1254_ = lean_apply_2(v_toPure_1246_, lean_box(0), v___x_1253_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(lean_object* v_f_1255_, lean_object* v_toBind_1256_, lean_object* v___f_1257_, lean_object* v_a_1258_, lean_object* v_x_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_apply_1(v_f_1255_, v_a_1258_);
v___x_1262_ = lean_apply_4(v_toBind_1256_, lean_box(0), lean_box(0), v___x_1261_, v___f_1257_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed(lean_object* v_f_1263_, lean_object* v_toBind_1264_, lean_object* v___f_1265_, lean_object* v_a_1266_, lean_object* v_x_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__5(v_f_1263_, v_toBind_1264_, v___f_1265_, v_a_1266_, v_x_1267_, v___y_1268_);
lean_dec_ref(v___y_1268_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed(lean_object* v_inst_1273_, lean_object* v_f_1274_, lean_object* v_toBind_1275_, lean_object* v___f_1276_, lean_object* v_a_1277_, lean_object* v_x_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(v_inst_1273_, v_f_1274_, v_toBind_1275_, v___f_1276_, v_a_1277_, v_x_1278_, v___y_1279_);
lean_dec_ref(v___y_1279_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg(lean_object* v_inst_1281_, lean_object* v_f_1282_, lean_object* v_x_1283_){
_start:
{
if (lean_obj_tag(v_x_1283_) == 0)
{
lean_object* v_toApplicative_1284_; lean_object* v_cs_1285_; lean_object* v_toBind_1286_; lean_object* v_toPure_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___f_1290_; lean_object* v___f_1291_; lean_object* v___f_1292_; size_t v_sz_1293_; size_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_toApplicative_1284_ = lean_ctor_get(v_inst_1281_, 0);
v_cs_1285_ = lean_ctor_get(v_x_1283_, 0);
lean_inc_ref(v_cs_1285_);
lean_dec_ref_known(v_x_1283_, 1);
v_toBind_1286_ = lean_ctor_get(v_inst_1281_, 1);
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
lean_inc_ref(v_inst_1281_);
v___f_1292_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__2___boxed), 7, 4);
lean_closure_set(v___f_1292_, 0, v_inst_1281_);
lean_closure_set(v___f_1292_, 1, v_f_1282_);
lean_closure_set(v___f_1292_, 2, v_toBind_1286_);
lean_closure_set(v___f_1292_, 3, v___f_1291_);
v_sz_1293_ = lean_array_size(v_cs_1285_);
v___x_1294_ = ((size_t)0ULL);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1281_, v_cs_1285_, v___f_1292_, v_sz_1293_, v___x_1294_, v___x_1289_);
v___x_1296_ = lean_apply_4(v_toBind_1286_, lean_box(0), lean_box(0), v___x_1295_, v___f_1290_);
return v___x_1296_;
}
else
{
lean_object* v_toApplicative_1297_; lean_object* v_vs_1298_; lean_object* v_toBind_1299_; lean_object* v_toPure_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___f_1303_; lean_object* v___f_1304_; lean_object* v___f_1305_; size_t v_sz_1306_; size_t v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_toApplicative_1297_ = lean_ctor_get(v_inst_1281_, 0);
v_vs_1298_ = lean_ctor_get(v_x_1283_, 0);
lean_inc_ref(v_vs_1298_);
lean_dec_ref_known(v_x_1283_, 1);
v_toBind_1299_ = lean_ctor_get(v_inst_1281_, 1);
lean_inc_n(v_toBind_1299_, 2);
v_toPure_1300_ = lean_ctor_get(v_toApplicative_1297_, 1);
v___x_1301_ = lean_box(0);
v___x_1302_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
lean_inc_n(v_toPure_1300_, 2);
v___f_1303_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1303_, 0, v_toPure_1300_);
v___f_1304_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1304_, 0, v___x_1301_);
lean_closure_set(v___f_1304_, 1, v_toPure_1300_);
lean_closure_set(v___f_1304_, 2, v___x_1302_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeMAux___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_1305_, 0, v_f_1282_);
lean_closure_set(v___f_1305_, 1, v_toBind_1299_);
lean_closure_set(v___f_1305_, 2, v___f_1304_);
v_sz_1306_ = lean_array_size(v_vs_1298_);
v___x_1307_ = ((size_t)0ULL);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1281_, v_vs_1298_, v___f_1305_, v_sz_1306_, v___x_1307_, v___x_1302_);
v___x_1309_ = lean_apply_4(v_toBind_1299_, lean_box(0), lean_box(0), v___x_1308_, v___f_1303_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___redArg___lam__2(lean_object* v_inst_1310_, lean_object* v_f_1311_, lean_object* v_toBind_1312_, lean_object* v___f_1313_, lean_object* v_a_1314_, lean_object* v_x_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1310_, v_f_1311_, v_a_1314_);
v___x_1318_ = lean_apply_4(v_toBind_1312_, lean_box(0), lean_box(0), v___x_1317_, v___f_1313_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux(lean_object* v_00_u03b1_1319_, lean_object* v_m_1320_, lean_object* v_inst_1321_, lean_object* v_00_u03b2_1322_, lean_object* v_f_1323_, lean_object* v_x_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1321_, v_f_1323_, v_x_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0(lean_object* v_toPure_1326_, lean_object* v_____do__lift_1327_, lean_object* v_____s_1328_){
_start:
{
lean_object* v_fst_1329_; 
v_fst_1329_ = lean_ctor_get(v_____s_1328_, 0);
lean_inc(v_fst_1329_);
lean_dec_ref(v_____s_1328_);
if (lean_obj_tag(v_fst_1329_) == 0)
{
lean_object* v___x_1330_; 
v___x_1330_ = lean_apply_2(v_toPure_1326_, lean_box(0), v_____do__lift_1327_);
return v___x_1330_;
}
else
{
lean_object* v_val_1331_; lean_object* v___x_1332_; 
lean_dec(v_____do__lift_1327_);
v_val_1331_ = lean_ctor_get(v_fst_1329_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v_fst_1329_, 1);
v___x_1332_ = lean_apply_2(v_toPure_1326_, lean_box(0), v_val_1331_);
return v___x_1332_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1(lean_object* v___x_1333_, lean_object* v_toPure_1334_, lean_object* v___x_1335_, lean_object* v_____do__lift_1336_){
_start:
{
if (lean_obj_tag(v_____do__lift_1336_) == 1)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
lean_dec_ref(v___x_1335_);
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_____do__lift_1336_);
v___x_1338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
lean_ctor_set(v___x_1338_, 1, v___x_1333_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
v___x_1340_ = lean_apply_2(v_toPure_1334_, lean_box(0), v___x_1339_);
return v___x_1340_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec(v_____do__lift_1336_);
v___x_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1335_);
v___x_1342_ = lean_apply_2(v_toPure_1334_, lean_box(0), v___x_1341_);
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(lean_object* v_f_1343_, lean_object* v_toBind_1344_, lean_object* v___f_1345_, lean_object* v_a_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1349_ = lean_apply_1(v_f_1343_, v_a_1346_);
v___x_1350_ = lean_apply_4(v_toBind_1344_, lean_box(0), lean_box(0), v___x_1349_, v___f_1345_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed(lean_object* v_f_1351_, lean_object* v_toBind_1352_, lean_object* v___f_1353_, lean_object* v_a_1354_, lean_object* v_x_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2(v_f_1351_, v_toBind_1352_, v___f_1353_, v_a_1354_, v_x_1355_, v___y_1356_);
lean_dec_ref(v___y_1356_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3(lean_object* v_toPure_1358_, lean_object* v_f_1359_, lean_object* v_toBind_1360_, lean_object* v_tail_1361_, lean_object* v_inst_1362_, lean_object* v_____do__lift_1363_){
_start:
{
if (lean_obj_tag(v_____do__lift_1363_) == 0)
{
lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___f_1367_; lean_object* v___f_1368_; size_t v_sz_1369_; size_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_inc(v_toPure_1358_);
v___f_1364_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1364_, 0, v_toPure_1358_);
lean_closure_set(v___f_1364_, 1, v_____do__lift_1363_);
v___x_1365_ = lean_box(0);
v___x_1366_ = ((lean_object*)(l_Lean_PersistentArray_findSomeMAux___redArg___closed__0));
v___f_1367_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__1), 4, 3);
lean_closure_set(v___f_1367_, 0, v___x_1365_);
lean_closure_set(v___f_1367_, 1, v_toPure_1358_);
lean_closure_set(v___f_1367_, 2, v___x_1366_);
lean_inc(v_toBind_1360_);
v___f_1368_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__2___boxed), 6, 3);
lean_closure_set(v___f_1368_, 0, v_f_1359_);
lean_closure_set(v___f_1368_, 1, v_toBind_1360_);
lean_closure_set(v___f_1368_, 2, v___f_1367_);
v_sz_1369_ = lean_array_size(v_tail_1361_);
v___x_1370_ = ((size_t)0ULL);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1362_, v_tail_1361_, v___f_1368_, v_sz_1369_, v___x_1370_, v___x_1366_);
v___x_1372_ = lean_apply_4(v_toBind_1360_, lean_box(0), lean_box(0), v___x_1371_, v___f_1364_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; 
lean_dec_ref(v_inst_1362_);
lean_dec_ref(v_tail_1361_);
lean_dec(v_toBind_1360_);
lean_dec(v_f_1359_);
v___x_1373_ = lean_apply_2(v_toPure_1358_, lean_box(0), v_____do__lift_1363_);
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___redArg(lean_object* v_inst_1374_, lean_object* v_t_1375_, lean_object* v_f_1376_){
_start:
{
lean_object* v_toApplicative_1377_; lean_object* v_toBind_1378_; lean_object* v_root_1379_; lean_object* v_tail_1380_; lean_object* v_toPure_1381_; lean_object* v___x_1382_; lean_object* v___f_1383_; lean_object* v___x_1384_; 
v_toApplicative_1377_ = lean_ctor_get(v_inst_1374_, 0);
v_toBind_1378_ = lean_ctor_get(v_inst_1374_, 1);
lean_inc_n(v_toBind_1378_, 2);
v_root_1379_ = lean_ctor_get(v_t_1375_, 0);
lean_inc_ref(v_root_1379_);
v_tail_1380_ = lean_ctor_get(v_t_1375_, 1);
lean_inc_ref(v_tail_1380_);
lean_dec_ref(v_t_1375_);
v_toPure_1381_ = lean_ctor_get(v_toApplicative_1377_, 1);
lean_inc(v_toPure_1381_);
lean_inc(v_f_1376_);
lean_inc_ref(v_inst_1374_);
v___x_1382_ = l_Lean_PersistentArray_findSomeMAux___redArg(v_inst_1374_, v_f_1376_, v_root_1379_);
v___f_1383_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeM_x3f___redArg___lam__3), 6, 5);
lean_closure_set(v___f_1383_, 0, v_toPure_1381_);
lean_closure_set(v___f_1383_, 1, v_f_1376_);
lean_closure_set(v___f_1383_, 2, v_toBind_1378_);
lean_closure_set(v___f_1383_, 3, v_tail_1380_);
lean_closure_set(v___f_1383_, 4, v_inst_1374_);
v___x_1384_ = lean_apply_4(v_toBind_1378_, lean_box(0), lean_box(0), v___x_1382_, v___f_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f(lean_object* v_00_u03b1_1385_, lean_object* v_m_1386_, lean_object* v_inst_1387_, lean_object* v_00_u03b2_1388_, lean_object* v_t_1389_, lean_object* v_f_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v_inst_1387_, v_t_1389_, v_f_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg(lean_object* v_inst_1392_, lean_object* v_f_1393_, lean_object* v_x_1394_){
_start:
{
if (lean_obj_tag(v_x_1394_) == 0)
{
lean_object* v_cs_1395_; lean_object* v___f_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v_cs_1395_ = lean_ctor_get(v_x_1394_, 0);
lean_inc_ref(v_cs_1395_);
lean_dec_ref_known(v_x_1394_, 1);
lean_inc_ref(v_inst_1392_);
v___f_1396_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_1396_, 0, v_inst_1392_);
lean_closure_set(v___f_1396_, 1, v_f_1393_);
v___x_1397_ = lean_array_get_size(v_cs_1395_);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1392_, v___f_1396_, v_cs_1395_, v___x_1397_, lean_box(0));
return v___x_1398_;
}
else
{
lean_object* v_vs_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v_vs_1399_ = lean_ctor_get(v_x_1394_, 0);
lean_inc_ref(v_vs_1399_);
lean_dec_ref_known(v_x_1394_, 1);
v___x_1400_ = lean_array_get_size(v_vs_1399_);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1392_, v_f_1393_, v_vs_1399_, v___x_1400_, lean_box(0));
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___redArg___lam__0(lean_object* v_inst_1402_, lean_object* v_f_1403_, lean_object* v_c_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1402_, v_f_1403_, v_c_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux(lean_object* v_00_u03b1_1406_, lean_object* v_m_1407_, lean_object* v_inst_1408_, lean_object* v_00_u03b2_1409_, lean_object* v_f_1410_, lean_object* v_x_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1408_, v_f_1410_, v_x_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0(lean_object* v_inst_1413_, lean_object* v_f_1414_, lean_object* v_root_1415_, lean_object* v_toPure_1416_, lean_object* v_____do__lift_1417_){
_start:
{
if (lean_obj_tag(v_____do__lift_1417_) == 0)
{
lean_object* v___x_1418_; 
lean_dec(v_toPure_1416_);
v___x_1418_ = l_Lean_PersistentArray_findSomeRevMAux___redArg(v_inst_1413_, v_f_1414_, v_root_1415_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; 
lean_dec_ref(v_root_1415_);
lean_dec(v_f_1414_);
lean_dec_ref(v_inst_1413_);
v___x_1419_ = lean_apply_2(v_toPure_1416_, lean_box(0), v_____do__lift_1417_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object* v_inst_1420_, lean_object* v_t_1421_, lean_object* v_f_1422_){
_start:
{
lean_object* v_toApplicative_1423_; lean_object* v_toBind_1424_; lean_object* v_root_1425_; lean_object* v_tail_1426_; lean_object* v_toPure_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___f_1430_; lean_object* v___x_1431_; 
v_toApplicative_1423_ = lean_ctor_get(v_inst_1420_, 0);
v_toBind_1424_ = lean_ctor_get(v_inst_1420_, 1);
lean_inc(v_toBind_1424_);
v_root_1425_ = lean_ctor_get(v_t_1421_, 0);
lean_inc_ref(v_root_1425_);
v_tail_1426_ = lean_ctor_get(v_t_1421_, 1);
lean_inc_ref(v_tail_1426_);
lean_dec_ref(v_t_1421_);
v_toPure_1427_ = lean_ctor_get(v_toApplicative_1423_, 1);
lean_inc(v_toPure_1427_);
v___x_1428_ = lean_array_get_size(v_tail_1426_);
lean_inc(v_f_1422_);
lean_inc_ref(v_inst_1420_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find(lean_box(0), lean_box(0), lean_box(0), v_inst_1420_, v_f_1422_, v_tail_1426_, v___x_1428_, lean_box(0));
v___f_1430_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSomeRevM_x3f___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1430_, 0, v_inst_1420_);
lean_closure_set(v___f_1430_, 1, v_f_1422_);
lean_closure_set(v___f_1430_, 2, v_root_1425_);
lean_closure_set(v___f_1430_, 3, v_toPure_1427_);
v___x_1431_ = lean_apply_4(v_toBind_1424_, lean_box(0), lean_box(0), v___x_1429_, v___f_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f(lean_object* v_00_u03b1_1432_, lean_object* v_m_1433_, lean_object* v_inst_1434_, lean_object* v_00_u03b2_1435_, lean_object* v_t_1436_, lean_object* v_f_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v_inst_1434_, v_t_1436_, v_f_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__1(lean_object* v_f_1439_, lean_object* v_x_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_apply_1(v_f_1439_, v___y_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg(lean_object* v_inst_1443_, lean_object* v_f_1444_, lean_object* v_x_1445_){
_start:
{
if (lean_obj_tag(v_x_1445_) == 0)
{
lean_object* v_toApplicative_1446_; lean_object* v_cs_1447_; lean_object* v_toPure_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_toApplicative_1446_ = lean_ctor_get(v_inst_1443_, 0);
v_cs_1447_ = lean_ctor_get(v_x_1445_, 0);
lean_inc_ref(v_cs_1447_);
lean_dec_ref_known(v_x_1445_, 1);
v_toPure_1448_ = lean_ctor_get(v_toApplicative_1446_, 1);
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = lean_array_get_size(v_cs_1447_);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_nat_dec_lt(v___x_1449_, v___x_1450_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
lean_inc(v_toPure_1448_);
lean_dec_ref(v_cs_1447_);
lean_dec(v_f_1444_);
lean_dec_ref(v_inst_1443_);
v___x_1453_ = lean_apply_2(v_toPure_1448_, lean_box(0), v___x_1451_);
return v___x_1453_;
}
else
{
lean_object* v___f_1454_; uint8_t v___x_1455_; 
lean_inc_ref(v_inst_1443_);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1454_, 0, v_inst_1443_);
lean_closure_set(v___f_1454_, 1, v_f_1444_);
v___x_1455_ = lean_nat_dec_le(v___x_1450_, v___x_1450_);
if (v___x_1455_ == 0)
{
if (v___x_1452_ == 0)
{
lean_object* v___x_1456_; 
lean_inc(v_toPure_1448_);
lean_dec_ref(v___f_1454_);
lean_dec_ref(v_cs_1447_);
lean_dec_ref(v_inst_1443_);
v___x_1456_ = lean_apply_2(v_toPure_1448_, lean_box(0), v___x_1451_);
return v___x_1456_;
}
else
{
size_t v___x_1457_; size_t v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = ((size_t)0ULL);
v___x_1458_ = lean_usize_of_nat(v___x_1450_);
v___x_1459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1443_, v___f_1454_, v_cs_1447_, v___x_1457_, v___x_1458_, v___x_1451_);
return v___x_1459_;
}
}
else
{
size_t v___x_1460_; size_t v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = ((size_t)0ULL);
v___x_1461_ = lean_usize_of_nat(v___x_1450_);
v___x_1462_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1443_, v___f_1454_, v_cs_1447_, v___x_1460_, v___x_1461_, v___x_1451_);
return v___x_1462_;
}
}
}
else
{
lean_object* v_toApplicative_1463_; lean_object* v_vs_1464_; lean_object* v_toPure_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_toApplicative_1463_ = lean_ctor_get(v_inst_1443_, 0);
v_vs_1464_ = lean_ctor_get(v_x_1445_, 0);
lean_inc_ref(v_vs_1464_);
lean_dec_ref_known(v_x_1445_, 1);
v_toPure_1465_ = lean_ctor_get(v_toApplicative_1463_, 1);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_array_get_size(v_vs_1464_);
v___x_1468_ = lean_box(0);
v___x_1469_ = lean_nat_dec_lt(v___x_1466_, v___x_1467_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; 
lean_inc(v_toPure_1465_);
lean_dec_ref(v_vs_1464_);
lean_dec(v_f_1444_);
lean_dec_ref(v_inst_1443_);
v___x_1470_ = lean_apply_2(v_toPure_1465_, lean_box(0), v___x_1468_);
return v___x_1470_;
}
else
{
lean_object* v___f_1471_; uint8_t v___x_1472_; 
v___f_1471_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1471_, 0, v_f_1444_);
v___x_1472_ = lean_nat_dec_le(v___x_1467_, v___x_1467_);
if (v___x_1472_ == 0)
{
if (v___x_1469_ == 0)
{
lean_object* v___x_1473_; 
lean_inc(v_toPure_1465_);
lean_dec_ref(v___f_1471_);
lean_dec_ref(v_vs_1464_);
lean_dec_ref(v_inst_1443_);
v___x_1473_ = lean_apply_2(v_toPure_1465_, lean_box(0), v___x_1468_);
return v___x_1473_;
}
else
{
size_t v___x_1474_; size_t v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = ((size_t)0ULL);
v___x_1475_ = lean_usize_of_nat(v___x_1467_);
v___x_1476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1443_, v___f_1471_, v_vs_1464_, v___x_1474_, v___x_1475_, v___x_1468_);
return v___x_1476_;
}
}
else
{
size_t v___x_1477_; size_t v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = ((size_t)0ULL);
v___x_1478_ = lean_usize_of_nat(v___x_1467_);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1443_, v___f_1471_, v_vs_1464_, v___x_1477_, v___x_1478_, v___x_1468_);
return v___x_1479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___redArg___lam__0(lean_object* v_inst_1480_, lean_object* v_f_1481_, lean_object* v_x_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1480_, v_f_1481_, v___y_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux(lean_object* v_00_u03b1_1485_, lean_object* v_m_1486_, lean_object* v_inst_1487_, lean_object* v_f_1488_, lean_object* v_x_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1487_, v_f_1488_, v_x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__0(lean_object* v_f_1491_, lean_object* v_x_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_apply_1(v_f_1491_, v___y_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg___lam__1(lean_object* v_tail_1495_, lean_object* v_toPure_1496_, lean_object* v_inst_1497_, lean_object* v___f_1498_, lean_object* v_x_1499_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1500_ = lean_unsigned_to_nat(0u);
v___x_1501_ = lean_array_get_size(v_tail_1495_);
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_nat_dec_lt(v___x_1500_, v___x_1501_);
if (v___x_1503_ == 0)
{
lean_object* v___x_1504_; 
lean_dec(v___f_1498_);
lean_dec_ref(v_inst_1497_);
lean_dec_ref(v_tail_1495_);
v___x_1504_ = lean_apply_2(v_toPure_1496_, lean_box(0), v___x_1502_);
return v___x_1504_;
}
else
{
uint8_t v___x_1505_; 
v___x_1505_ = lean_nat_dec_le(v___x_1501_, v___x_1501_);
if (v___x_1505_ == 0)
{
if (v___x_1503_ == 0)
{
lean_object* v___x_1506_; 
lean_dec(v___f_1498_);
lean_dec_ref(v_inst_1497_);
lean_dec_ref(v_tail_1495_);
v___x_1506_ = lean_apply_2(v_toPure_1496_, lean_box(0), v___x_1502_);
return v___x_1506_;
}
else
{
size_t v___x_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
lean_dec(v_toPure_1496_);
v___x_1507_ = ((size_t)0ULL);
v___x_1508_ = lean_usize_of_nat(v___x_1501_);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1497_, v___f_1498_, v_tail_1495_, v___x_1507_, v___x_1508_, v___x_1502_);
return v___x_1509_;
}
}
else
{
size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
lean_dec(v_toPure_1496_);
v___x_1510_ = ((size_t)0ULL);
v___x_1511_ = lean_usize_of_nat(v___x_1501_);
v___x_1512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1497_, v___f_1498_, v_tail_1495_, v___x_1510_, v___x_1511_, v___x_1502_);
return v___x_1512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0___redArg(lean_object* v_inst_1513_, lean_object* v_t_1514_, lean_object* v_f_1515_){
_start:
{
lean_object* v_toApplicative_1516_; lean_object* v_toPure_1517_; lean_object* v_toSeqRight_1518_; lean_object* v_root_1519_; lean_object* v_tail_1520_; lean_object* v___f_1521_; lean_object* v___f_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_toApplicative_1516_ = lean_ctor_get(v_inst_1513_, 0);
v_toPure_1517_ = lean_ctor_get(v_toApplicative_1516_, 1);
v_toSeqRight_1518_ = lean_ctor_get(v_toApplicative_1516_, 4);
lean_inc(v_toSeqRight_1518_);
v_root_1519_ = lean_ctor_get(v_t_1514_, 0);
lean_inc_ref(v_root_1519_);
v_tail_1520_ = lean_ctor_get(v_t_1514_, 1);
lean_inc_ref(v_tail_1520_);
lean_dec_ref(v_t_1514_);
lean_inc(v_f_1515_);
v___f_1521_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1521_, 0, v_f_1515_);
lean_inc_ref(v_inst_1513_);
lean_inc(v_toPure_1517_);
v___f_1522_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__1), 5, 4);
lean_closure_set(v___f_1522_, 0, v_tail_1520_);
lean_closure_set(v___f_1522_, 1, v_toPure_1517_);
lean_closure_set(v___f_1522_, 2, v_inst_1513_);
lean_closure_set(v___f_1522_, 3, v___f_1521_);
v___x_1523_ = l_Lean_PersistentArray_forMAux___redArg(v_inst_1513_, v_f_1515_, v_root_1519_);
v___x_1524_ = lean_apply_4(v_toSeqRight_1518_, lean_box(0), lean_box(0), v___x_1523_, v___f_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMFrom0(lean_object* v_00_u03b1_1525_, lean_object* v_m_1526_, lean_object* v_inst_1527_, lean_object* v_t_1528_, lean_object* v_f_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1527_, v_t_1528_, v_f_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(lean_object* v_toApplicative_1531_, lean_object* v_j_1532_, lean_object* v_cs_1533_, lean_object* v_inst_1534_, lean_object* v___f_1535_, lean_object* v_____r_1536_){
_start:
{
lean_object* v_toPure_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v_toPure_1537_ = lean_ctor_get(v_toApplicative_1531_, 1);
lean_inc(v_toPure_1537_);
lean_dec_ref(v_toApplicative_1531_);
v___x_1538_ = lean_unsigned_to_nat(1u);
v___x_1539_ = lean_nat_add(v_j_1532_, v___x_1538_);
v___x_1540_ = lean_array_get_size(v_cs_1533_);
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_nat_dec_lt(v___x_1539_, v___x_1540_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
lean_dec(v___x_1539_);
lean_dec(v___f_1535_);
lean_dec_ref(v_inst_1534_);
lean_dec_ref(v_cs_1533_);
v___x_1543_ = lean_apply_2(v_toPure_1537_, lean_box(0), v___x_1541_);
return v___x_1543_;
}
else
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_nat_dec_le(v___x_1540_, v___x_1540_);
if (v___x_1544_ == 0)
{
if (v___x_1542_ == 0)
{
lean_object* v___x_1545_; 
lean_dec(v___x_1539_);
lean_dec(v___f_1535_);
lean_dec_ref(v_inst_1534_);
lean_dec_ref(v_cs_1533_);
v___x_1545_ = lean_apply_2(v_toPure_1537_, lean_box(0), v___x_1541_);
return v___x_1545_;
}
else
{
size_t v___x_1546_; size_t v___x_1547_; lean_object* v___x_1548_; 
lean_dec(v_toPure_1537_);
v___x_1546_ = lean_usize_of_nat(v___x_1539_);
lean_dec(v___x_1539_);
v___x_1547_ = lean_usize_of_nat(v___x_1540_);
v___x_1548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1534_, v___f_1535_, v_cs_1533_, v___x_1546_, v___x_1547_, v___x_1541_);
return v___x_1548_;
}
}
else
{
size_t v___x_1549_; size_t v___x_1550_; lean_object* v___x_1551_; 
lean_dec(v_toPure_1537_);
v___x_1549_ = lean_usize_of_nat(v___x_1539_);
lean_dec(v___x_1539_);
v___x_1550_ = lean_usize_of_nat(v___x_1540_);
v___x_1551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1534_, v___f_1535_, v_cs_1533_, v___x_1549_, v___x_1550_, v___x_1541_);
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed(lean_object* v_toApplicative_1552_, lean_object* v_j_1553_, lean_object* v_cs_1554_, lean_object* v_inst_1555_, lean_object* v___f_1556_, lean_object* v_____r_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1(v_toApplicative_1552_, v_j_1553_, v_cs_1554_, v_inst_1555_, v___f_1556_, v_____r_1557_);
lean_dec(v_j_1553_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(lean_object* v_inst_1559_, lean_object* v_f_1560_, lean_object* v_x_1561_, size_t v_x_1562_, size_t v_x_1563_){
_start:
{
if (lean_obj_tag(v_x_1561_) == 0)
{
lean_object* v_toApplicative_1564_; lean_object* v_toBind_1565_; lean_object* v_cs_1566_; lean_object* v___f_1567_; lean_object* v___x_1568_; size_t v___x_1569_; lean_object* v_j_1570_; lean_object* v___f_1571_; lean_object* v___x_1572_; size_t v___x_1573_; size_t v___x_1574_; size_t v___x_1575_; size_t v___x_1576_; size_t v___x_1577_; size_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_toApplicative_1564_ = lean_ctor_get(v_inst_1559_, 0);
v_toBind_1565_ = lean_ctor_get(v_inst_1559_, 1);
lean_inc(v_toBind_1565_);
v_cs_1566_ = lean_ctor_get(v_x_1561_, 0);
lean_inc_ref_n(v_cs_1566_, 2);
lean_dec_ref_known(v_x_1561_, 1);
lean_inc(v_f_1560_);
lean_inc_ref_n(v_inst_1559_, 2);
v___f_1567_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1567_, 0, v_inst_1559_);
lean_closure_set(v___f_1567_, 1, v_f_1560_);
v___x_1568_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_1569_ = lean_usize_shift_right(v_x_1562_, v_x_1563_);
v_j_1570_ = lean_usize_to_nat(v___x_1569_);
lean_inc(v_j_1570_);
lean_inc_ref(v_toApplicative_1564_);
v___f_1571_ = lean_alloc_closure((void*)(l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1571_, 0, v_toApplicative_1564_);
lean_closure_set(v___f_1571_, 1, v_j_1570_);
lean_closure_set(v___f_1571_, 2, v_cs_1566_);
lean_closure_set(v___f_1571_, 3, v_inst_1559_);
lean_closure_set(v___f_1571_, 4, v___f_1567_);
v___x_1572_ = lean_array_get(v___x_1568_, v_cs_1566_, v_j_1570_);
lean_dec(v_j_1570_);
lean_dec_ref(v_cs_1566_);
v___x_1573_ = ((size_t)1ULL);
v___x_1574_ = lean_usize_shift_left(v___x_1573_, v_x_1563_);
v___x_1575_ = lean_usize_sub(v___x_1574_, v___x_1573_);
v___x_1576_ = lean_usize_land(v_x_1562_, v___x_1575_);
v___x_1577_ = ((size_t)5ULL);
v___x_1578_ = lean_usize_sub(v_x_1563_, v___x_1577_);
v___x_1579_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1559_, v_f_1560_, v___x_1572_, v___x_1576_, v___x_1578_);
v___x_1580_ = lean_apply_4(v_toBind_1565_, lean_box(0), lean_box(0), v___x_1579_, v___f_1571_);
return v___x_1580_;
}
else
{
lean_object* v_toApplicative_1581_; lean_object* v_vs_1582_; lean_object* v_toPure_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v_toApplicative_1581_ = lean_ctor_get(v_inst_1559_, 0);
v_vs_1582_ = lean_ctor_get(v_x_1561_, 0);
lean_inc_ref(v_vs_1582_);
lean_dec_ref_known(v_x_1561_, 1);
v_toPure_1583_ = lean_ctor_get(v_toApplicative_1581_, 1);
v___x_1584_ = lean_usize_to_nat(v_x_1562_);
v___x_1585_ = lean_array_get_size(v_vs_1582_);
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_nat_dec_lt(v___x_1584_, v___x_1585_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
lean_inc(v_toPure_1583_);
lean_dec(v___x_1584_);
lean_dec_ref(v_vs_1582_);
lean_dec(v_f_1560_);
lean_dec_ref(v_inst_1559_);
v___x_1588_ = lean_apply_2(v_toPure_1583_, lean_box(0), v___x_1586_);
return v___x_1588_;
}
else
{
lean_object* v___f_1589_; uint8_t v___x_1590_; 
v___f_1589_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMAux___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1589_, 0, v_f_1560_);
v___x_1590_ = lean_nat_dec_le(v___x_1585_, v___x_1585_);
if (v___x_1590_ == 0)
{
if (v___x_1587_ == 0)
{
lean_object* v___x_1591_; 
lean_inc(v_toPure_1583_);
lean_dec_ref(v___f_1589_);
lean_dec(v___x_1584_);
lean_dec_ref(v_vs_1582_);
lean_dec_ref(v_inst_1559_);
v___x_1591_ = lean_apply_2(v_toPure_1583_, lean_box(0), v___x_1586_);
return v___x_1591_;
}
else
{
size_t v___x_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = lean_usize_of_nat(v___x_1584_);
lean_dec(v___x_1584_);
v___x_1593_ = lean_usize_of_nat(v___x_1585_);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1559_, v___f_1589_, v_vs_1582_, v___x_1592_, v___x_1593_, v___x_1586_);
return v___x_1594_;
}
}
else
{
size_t v___x_1595_; size_t v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = lean_usize_of_nat(v___x_1584_);
lean_dec(v___x_1584_);
v___x_1596_ = lean_usize_of_nat(v___x_1585_);
v___x_1597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1559_, v___f_1589_, v_vs_1582_, v___x_1595_, v___x_1596_, v___x_1586_);
return v___x_1597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg___boxed(lean_object* v_inst_1598_, lean_object* v_f_1599_, lean_object* v_x_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_){
_start:
{
size_t v_x_271__boxed_1603_; size_t v_x_272__boxed_1604_; lean_object* v_res_1605_; 
v_x_271__boxed_1603_ = lean_unbox_usize(v_x_1601_);
lean_dec(v_x_1601_);
v_x_272__boxed_1604_ = lean_unbox_usize(v_x_1602_);
lean_dec(v_x_1602_);
v_res_1605_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1598_, v_f_1599_, v_x_1600_, v_x_271__boxed_1603_, v_x_272__boxed_1604_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(lean_object* v_00_u03b1_1606_, lean_object* v_m_1607_, lean_object* v_inst_1608_, lean_object* v_f_1609_, lean_object* v_x_1610_, size_t v_x_1611_, size_t v_x_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1608_, v_f_1609_, v_x_1610_, v_x_1611_, v_x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___boxed(lean_object* v_00_u03b1_1614_, lean_object* v_m_1615_, lean_object* v_inst_1616_, lean_object* v_f_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
size_t v_x_341__boxed_1621_; size_t v_x_342__boxed_1622_; lean_object* v_res_1623_; 
v_x_341__boxed_1621_ = lean_unbox_usize(v_x_1619_);
lean_dec(v_x_1619_);
v_x_342__boxed_1622_ = lean_unbox_usize(v_x_1620_);
lean_dec(v_x_1620_);
v_res_1623_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux(v_00_u03b1_1614_, v_m_1615_, v_inst_1616_, v_f_1617_, v_x_1618_, v_x_341__boxed_1621_, v_x_342__boxed_1622_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1(lean_object* v_toApplicative_1624_, lean_object* v_tail_1625_, lean_object* v___x_1626_, lean_object* v_inst_1627_, lean_object* v___f_1628_, lean_object* v_____r_1629_){
_start:
{
lean_object* v_toPure_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v_toPure_1630_ = lean_ctor_get(v_toApplicative_1624_, 1);
lean_inc(v_toPure_1630_);
lean_dec_ref(v_toApplicative_1624_);
v___x_1631_ = lean_array_get_size(v_tail_1625_);
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_nat_dec_lt(v___x_1626_, v___x_1631_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec(v___f_1628_);
lean_dec_ref(v_inst_1627_);
lean_dec_ref(v_tail_1625_);
v___x_1634_ = lean_apply_2(v_toPure_1630_, lean_box(0), v___x_1632_);
return v___x_1634_;
}
else
{
uint8_t v___x_1635_; 
v___x_1635_ = lean_nat_dec_le(v___x_1631_, v___x_1631_);
if (v___x_1635_ == 0)
{
if (v___x_1633_ == 0)
{
lean_object* v___x_1636_; 
lean_dec(v___f_1628_);
lean_dec_ref(v_inst_1627_);
lean_dec_ref(v_tail_1625_);
v___x_1636_ = lean_apply_2(v_toPure_1630_, lean_box(0), v___x_1632_);
return v___x_1636_;
}
else
{
size_t v___x_1637_; size_t v___x_1638_; lean_object* v___x_1639_; 
lean_dec(v_toPure_1630_);
v___x_1637_ = ((size_t)0ULL);
v___x_1638_ = lean_usize_of_nat(v___x_1631_);
v___x_1639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1627_, v___f_1628_, v_tail_1625_, v___x_1637_, v___x_1638_, v___x_1632_);
return v___x_1639_;
}
}
else
{
size_t v___x_1640_; size_t v___x_1641_; lean_object* v___x_1642_; 
lean_dec(v_toPure_1630_);
v___x_1640_ = ((size_t)0ULL);
v___x_1641_ = lean_usize_of_nat(v___x_1631_);
v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1627_, v___f_1628_, v_tail_1625_, v___x_1640_, v___x_1641_, v___x_1632_);
return v___x_1642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___lam__1___boxed(lean_object* v_toApplicative_1643_, lean_object* v_tail_1644_, lean_object* v___x_1645_, lean_object* v_inst_1646_, lean_object* v___f_1647_, lean_object* v_____r_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_PersistentArray_forM___redArg___lam__1(v_toApplicative_1643_, v_tail_1644_, v___x_1645_, v_inst_1646_, v___f_1647_, v_____r_1648_);
lean_dec(v___x_1645_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg(lean_object* v_inst_1650_, lean_object* v_t_1651_, lean_object* v_f_1652_, lean_object* v_start_1653_){
_start:
{
lean_object* v_toApplicative_1654_; lean_object* v_toBind_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v_toApplicative_1654_ = lean_ctor_get(v_inst_1650_, 0);
v_toBind_1655_ = lean_ctor_get(v_inst_1650_, 1);
v___x_1656_ = lean_unsigned_to_nat(0u);
v___x_1657_ = lean_nat_dec_eq(v_start_1653_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v_root_1658_; lean_object* v_tail_1659_; size_t v_shift_1660_; lean_object* v_tailOff_1661_; uint8_t v___x_1662_; 
v_root_1658_ = lean_ctor_get(v_t_1651_, 0);
lean_inc_ref(v_root_1658_);
v_tail_1659_ = lean_ctor_get(v_t_1651_, 1);
lean_inc_ref(v_tail_1659_);
v_shift_1660_ = lean_ctor_get_usize(v_t_1651_, 4);
v_tailOff_1661_ = lean_ctor_get(v_t_1651_, 3);
lean_inc(v_tailOff_1661_);
lean_dec_ref(v_t_1651_);
v___x_1662_ = lean_nat_dec_le(v_tailOff_1661_, v_start_1653_);
if (v___x_1662_ == 0)
{
lean_object* v___f_1663_; lean_object* v___f_1664_; size_t v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_inc(v_toBind_1655_);
lean_dec(v_tailOff_1661_);
lean_inc(v_f_1652_);
v___f_1663_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1663_, 0, v_f_1652_);
lean_inc_ref(v_inst_1650_);
lean_inc_ref(v_toApplicative_1654_);
v___f_1664_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forM___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_1664_, 0, v_toApplicative_1654_);
lean_closure_set(v___f_1664_, 1, v_tail_1659_);
lean_closure_set(v___f_1664_, 2, v___x_1656_);
lean_closure_set(v___f_1664_, 3, v_inst_1650_);
lean_closure_set(v___f_1664_, 4, v___f_1663_);
v___x_1665_ = lean_usize_of_nat(v_start_1653_);
v___x_1666_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_forFromMAux___redArg(v_inst_1650_, v_f_1652_, v_root_1658_, v___x_1665_, v_shift_1660_);
v___x_1667_ = lean_apply_4(v_toBind_1655_, lean_box(0), lean_box(0), v___x_1666_, v___f_1664_);
return v___x_1667_;
}
else
{
lean_object* v_toPure_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; 
lean_dec_ref(v_root_1658_);
v_toPure_1668_ = lean_ctor_get(v_toApplicative_1654_, 1);
v___x_1669_ = lean_nat_sub(v_start_1653_, v_tailOff_1661_);
lean_dec(v_tailOff_1661_);
v___x_1670_ = lean_array_get_size(v_tail_1659_);
v___x_1671_ = lean_box(0);
v___x_1672_ = lean_nat_dec_lt(v___x_1669_, v___x_1670_);
if (v___x_1672_ == 0)
{
lean_object* v___x_1673_; 
lean_inc(v_toPure_1668_);
lean_dec(v___x_1669_);
lean_dec_ref(v_tail_1659_);
lean_dec(v_f_1652_);
lean_dec_ref(v_inst_1650_);
v___x_1673_ = lean_apply_2(v_toPure_1668_, lean_box(0), v___x_1671_);
return v___x_1673_;
}
else
{
lean_object* v___f_1674_; uint8_t v___x_1675_; 
v___f_1674_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_forMFrom0___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1674_, 0, v_f_1652_);
v___x_1675_ = lean_nat_dec_le(v___x_1670_, v___x_1670_);
if (v___x_1675_ == 0)
{
if (v___x_1672_ == 0)
{
lean_object* v___x_1676_; 
lean_inc(v_toPure_1668_);
lean_dec_ref(v___f_1674_);
lean_dec(v___x_1669_);
lean_dec_ref(v_tail_1659_);
lean_dec_ref(v_inst_1650_);
v___x_1676_ = lean_apply_2(v_toPure_1668_, lean_box(0), v___x_1671_);
return v___x_1676_;
}
else
{
size_t v___x_1677_; size_t v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = lean_usize_of_nat(v___x_1669_);
lean_dec(v___x_1669_);
v___x_1678_ = lean_usize_of_nat(v___x_1670_);
v___x_1679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1650_, v___f_1674_, v_tail_1659_, v___x_1677_, v___x_1678_, v___x_1671_);
return v___x_1679_;
}
}
else
{
size_t v___x_1680_; size_t v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = lean_usize_of_nat(v___x_1669_);
lean_dec(v___x_1669_);
v___x_1681_ = lean_usize_of_nat(v___x_1670_);
v___x_1682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1650_, v___f_1674_, v_tail_1659_, v___x_1680_, v___x_1681_, v___x_1671_);
return v___x_1682_;
}
}
}
}
else
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Lean_PersistentArray_forMFrom0___redArg(v_inst_1650_, v_t_1651_, v_f_1652_);
return v___x_1683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___redArg___boxed(lean_object* v_inst_1684_, lean_object* v_t_1685_, lean_object* v_f_1686_, lean_object* v_start_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_PersistentArray_forM___redArg(v_inst_1684_, v_t_1685_, v_f_1686_, v_start_1687_);
lean_dec(v_start_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM(lean_object* v_00_u03b1_1689_, lean_object* v_m_1690_, lean_object* v_inst_1691_, lean_object* v_t_1692_, lean_object* v_f_1693_, lean_object* v_start_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_PersistentArray_forM___redArg(v_inst_1691_, v_t_1692_, v_f_1693_, v_start_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___boxed(lean_object* v_00_u03b1_1696_, lean_object* v_m_1697_, lean_object* v_inst_1698_, lean_object* v_t_1699_, lean_object* v_f_1700_, lean_object* v_start_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_PersistentArray_forM(v_00_u03b1_1696_, v_m_1697_, v_inst_1698_, v_t_1699_, v_f_1700_, v_start_1701_);
lean_dec(v_start_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___lam__0(lean_object* v_f_1703_, lean_object* v_x1_1704_, lean_object* v_x2_1705_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_apply_2(v_f_1703_, v_x1_1704_, v_x2_1705_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg(lean_object* v_t_1726_, lean_object* v_f_1727_, lean_object* v_init_1728_, lean_object* v_start_1729_){
_start:
{
lean_object* v___f_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___f_1730_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1730_, 0, v_f_1727_);
v___x_1731_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1732_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1731_, v_t_1726_, v___f_1730_, v_init_1728_, v_start_1729_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___redArg___boxed(lean_object* v_t_1733_, lean_object* v_f_1734_, lean_object* v_init_1735_, lean_object* v_start_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lean_PersistentArray_foldl___redArg(v_t_1733_, v_f_1734_, v_init_1735_, v_start_1736_);
lean_dec(v_start_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl(lean_object* v_00_u03b1_1738_, lean_object* v_00_u03b2_1739_, lean_object* v_t_1740_, lean_object* v_f_1741_, lean_object* v_init_1742_, lean_object* v_start_1743_){
_start:
{
lean_object* v___f_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___f_1744_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1744_, 0, v_f_1741_);
v___x_1745_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1746_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1745_, v_t_1740_, v___f_1744_, v_init_1742_, v_start_1743_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldl___boxed(lean_object* v_00_u03b1_1747_, lean_object* v_00_u03b2_1748_, lean_object* v_t_1749_, lean_object* v_f_1750_, lean_object* v_init_1751_, lean_object* v_start_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_PersistentArray_foldl(v_00_u03b1_1747_, v_00_u03b2_1748_, v_t_1749_, v_f_1750_, v_init_1751_, v_start_1752_);
lean_dec(v_start_1752_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr___redArg(lean_object* v_t_1754_, lean_object* v_f_1755_, lean_object* v_init_1756_){
_start:
{
lean_object* v___f_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___f_1757_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1757_, 0, v_f_1755_);
v___x_1758_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1759_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1758_, v_t_1754_, v___f_1757_, v_init_1756_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldr(lean_object* v_00_u03b1_1760_, lean_object* v_00_u03b2_1761_, lean_object* v_t_1762_, lean_object* v_f_1763_, lean_object* v_init_1764_){
_start:
{
lean_object* v___f_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___f_1765_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_foldl___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1765_, 0, v_f_1763_);
v___x_1766_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1767_ = l_Lean_PersistentArray_foldrM___redArg(v___x_1766_, v_t_1762_, v___f_1765_, v_init_1764_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg___lam__0(lean_object* v_p_1768_, lean_object* v_x1_1769_, lean_object* v_x2_1770_){
_start:
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
lean_inc(v_x2_1770_);
v___x_1771_ = lean_apply_1(v_p_1768_, v_x2_1770_);
v___x_1772_ = lean_unbox(v___x_1771_);
if (v___x_1772_ == 0)
{
lean_dec(v_x2_1770_);
return v_x1_1769_;
}
else
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_PersistentArray_push___redArg(v_x1_1769_, v_x2_1770_);
return v___x_1773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter___redArg(lean_object* v_as_1774_, lean_object* v_p_1775_){
_start:
{
lean_object* v___f_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___f_1776_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1776_, 0, v_p_1775_);
v___x_1777_ = lean_unsigned_to_nat(32u);
v___x_1778_ = lean_mk_empty_array_with_capacity(v___x_1777_);
lean_dec_ref(v___x_1778_);
v___x_1779_ = lean_unsigned_to_nat(0u);
v___x_1780_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
v___x_1781_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1782_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1781_, v_as_1774_, v___f_1776_, v___x_1780_, v___x_1779_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_filter(lean_object* v_00_u03b1_1783_, lean_object* v_as_1784_, lean_object* v_p_1785_){
_start:
{
lean_object* v___f_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___f_1786_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_filter___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1786_, 0, v_p_1785_);
v___x_1787_ = lean_unsigned_to_nat(32u);
v___x_1788_ = lean_mk_empty_array_with_capacity(v___x_1787_);
lean_dec_ref(v___x_1788_);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
v___x_1791_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_1792_ = l_Lean_PersistentArray_foldlM___redArg(v___x_1791_, v_as_1784_, v___f_1786_, v___x_1790_, v___x_1789_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(lean_object* v_as_1793_, size_t v_i_1794_, size_t v_stop_1795_, lean_object* v_b_1796_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_usize_dec_eq(v_i_1794_, v_stop_1795_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; size_t v___x_1800_; size_t v___x_1801_; 
v___x_1798_ = lean_array_uget_borrowed(v_as_1793_, v_i_1794_);
lean_inc(v___x_1798_);
v___x_1799_ = lean_array_push(v_b_1796_, v___x_1798_);
v___x_1800_ = ((size_t)1ULL);
v___x_1801_ = lean_usize_add(v_i_1794_, v___x_1800_);
v_i_1794_ = v___x_1801_;
v_b_1796_ = v___x_1799_;
goto _start;
}
else
{
return v_b_1796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg___boxed(lean_object* v_as_1803_, lean_object* v_i_1804_, lean_object* v_stop_1805_, lean_object* v_b_1806_){
_start:
{
size_t v_i_boxed_1807_; size_t v_stop_boxed_1808_; lean_object* v_res_1809_; 
v_i_boxed_1807_ = lean_unbox_usize(v_i_1804_);
lean_dec(v_i_1804_);
v_stop_boxed_1808_ = lean_unbox_usize(v_stop_1805_);
lean_dec(v_stop_1805_);
v_res_1809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1803_, v_i_boxed_1807_, v_stop_boxed_1808_, v_b_1806_);
lean_dec_ref(v_as_1803_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
if (lean_obj_tag(v_x_1810_) == 0)
{
lean_object* v_cs_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v_cs_1812_ = lean_ctor_get(v_x_1810_, 0);
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_array_get_size(v_cs_1812_);
v___x_1815_ = lean_nat_dec_lt(v___x_1813_, v___x_1814_);
if (v___x_1815_ == 0)
{
return v_x_1811_;
}
else
{
size_t v___x_1816_; size_t v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = lean_usize_of_nat(v___x_1814_);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1812_, v___x_1816_, v___x_1817_, v_x_1811_);
return v___x_1818_;
}
}
else
{
lean_object* v_vs_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v_vs_1819_ = lean_ctor_get(v_x_1810_, 0);
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = lean_array_get_size(v_vs_1819_);
v___x_1822_ = lean_nat_dec_lt(v___x_1820_, v___x_1821_);
if (v___x_1822_ == 0)
{
return v_x_1811_;
}
else
{
size_t v___x_1823_; size_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = lean_usize_of_nat(v___x_1821_);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1819_, v___x_1823_, v___x_1824_, v_x_1811_);
return v___x_1825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(lean_object* v_as_1826_, size_t v_i_1827_, size_t v_stop_1828_, lean_object* v_b_1829_){
_start:
{
uint8_t v___x_1830_; 
v___x_1830_ = lean_usize_dec_eq(v_i_1827_, v_stop_1828_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; lean_object* v___x_1832_; size_t v___x_1833_; size_t v___x_1834_; 
v___x_1831_ = lean_array_uget_borrowed(v_as_1826_, v_i_1827_);
v___x_1832_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v___x_1831_, v_b_1829_);
v___x_1833_ = ((size_t)1ULL);
v___x_1834_ = lean_usize_add(v_i_1827_, v___x_1833_);
v_i_1827_ = v___x_1834_;
v_b_1829_ = v___x_1832_;
goto _start;
}
else
{
return v_b_1829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_1836_, lean_object* v_i_1837_, lean_object* v_stop_1838_, lean_object* v_b_1839_){
_start:
{
size_t v_i_boxed_1840_; size_t v_stop_boxed_1841_; lean_object* v_res_1842_; 
v_i_boxed_1840_ = lean_unbox_usize(v_i_1837_);
lean_dec(v_i_1837_);
v_stop_boxed_1841_ = lean_unbox_usize(v_stop_1838_);
lean_dec(v_stop_1838_);
v_res_1842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1836_, v_i_boxed_1840_, v_stop_boxed_1841_, v_b_1839_);
lean_dec_ref(v_as_1836_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg___boxed(lean_object* v_x_1843_, lean_object* v_x_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1843_, v_x_1844_);
lean_dec_ref(v_x_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(lean_object* v_x_1846_, size_t v_x_1847_, size_t v_x_1848_, lean_object* v_x_1849_){
_start:
{
if (lean_obj_tag(v_x_1846_) == 0)
{
lean_object* v_cs_1850_; lean_object* v___x_1851_; size_t v___x_1852_; lean_object* v_j_1853_; lean_object* v___x_1854_; size_t v___x_1855_; size_t v___x_1856_; size_t v___x_1857_; size_t v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; uint8_t v___x_1865_; 
v_cs_1850_ = lean_ctor_get(v_x_1846_, 0);
v___x_1851_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_1852_ = lean_usize_shift_right(v_x_1847_, v_x_1848_);
v_j_1853_ = lean_usize_to_nat(v___x_1852_);
v___x_1854_ = lean_array_get_borrowed(v___x_1851_, v_cs_1850_, v_j_1853_);
v___x_1855_ = ((size_t)1ULL);
v___x_1856_ = lean_usize_shift_left(v___x_1855_, v_x_1848_);
v___x_1857_ = lean_usize_sub(v___x_1856_, v___x_1855_);
v___x_1858_ = lean_usize_land(v_x_1847_, v___x_1857_);
v___x_1859_ = ((size_t)5ULL);
v___x_1860_ = lean_usize_sub(v_x_1848_, v___x_1859_);
v___x_1861_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v___x_1854_, v___x_1858_, v___x_1860_, v_x_1849_);
v___x_1862_ = lean_unsigned_to_nat(1u);
v___x_1863_ = lean_nat_add(v_j_1853_, v___x_1862_);
lean_dec(v_j_1853_);
v___x_1864_ = lean_array_get_size(v_cs_1850_);
v___x_1865_ = lean_nat_dec_lt(v___x_1863_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_dec(v___x_1863_);
return v___x_1861_;
}
else
{
size_t v___x_1866_; size_t v___x_1867_; lean_object* v___x_1868_; 
v___x_1866_ = lean_usize_of_nat(v___x_1863_);
lean_dec(v___x_1863_);
v___x_1867_ = lean_usize_of_nat(v___x_1864_);
v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_cs_1850_, v___x_1866_, v___x_1867_, v___x_1861_);
return v___x_1868_;
}
}
else
{
lean_object* v_vs_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v_vs_1869_ = lean_ctor_get(v_x_1846_, 0);
v___x_1870_ = lean_usize_to_nat(v_x_1847_);
v___x_1871_ = lean_array_get_size(v_vs_1869_);
v___x_1872_ = lean_nat_dec_lt(v___x_1870_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_dec(v___x_1870_);
return v_x_1849_;
}
else
{
size_t v___x_1873_; size_t v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = lean_usize_of_nat(v___x_1870_);
lean_dec(v___x_1870_);
v___x_1874_ = lean_usize_of_nat(v___x_1871_);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_vs_1869_, v___x_1873_, v___x_1874_, v_x_1849_);
return v___x_1875_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg___boxed(lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
size_t v_x_1118__boxed_1880_; size_t v_x_1119__boxed_1881_; lean_object* v_res_1882_; 
v_x_1118__boxed_1880_ = lean_unbox_usize(v_x_1877_);
lean_dec(v_x_1877_);
v_x_1119__boxed_1881_ = lean_unbox_usize(v_x_1878_);
lean_dec(v_x_1878_);
v_res_1882_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1876_, v_x_1118__boxed_1880_, v_x_1119__boxed_1881_, v_x_1879_);
lean_dec_ref(v_x_1876_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(lean_object* v_t_1883_, lean_object* v_init_1884_, lean_object* v_start_1885_){
_start:
{
lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = lean_nat_dec_eq(v_start_1885_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v_root_1888_; lean_object* v_tail_1889_; size_t v_shift_1890_; lean_object* v_tailOff_1891_; uint8_t v___x_1892_; 
v_root_1888_ = lean_ctor_get(v_t_1883_, 0);
v_tail_1889_ = lean_ctor_get(v_t_1883_, 1);
v_shift_1890_ = lean_ctor_get_usize(v_t_1883_, 4);
v_tailOff_1891_ = lean_ctor_get(v_t_1883_, 3);
v___x_1892_ = lean_nat_dec_le(v_tailOff_1891_, v_start_1885_);
if (v___x_1892_ == 0)
{
size_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1893_ = lean_usize_of_nat(v_start_1885_);
v___x_1894_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_root_1888_, v___x_1893_, v_shift_1890_, v_init_1884_);
v___x_1895_ = lean_array_get_size(v_tail_1889_);
v___x_1896_ = lean_nat_dec_lt(v___x_1886_, v___x_1895_);
if (v___x_1896_ == 0)
{
return v___x_1894_;
}
else
{
size_t v___x_1897_; size_t v___x_1898_; lean_object* v___x_1899_; 
v___x_1897_ = ((size_t)0ULL);
v___x_1898_ = lean_usize_of_nat(v___x_1895_);
v___x_1899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1889_, v___x_1897_, v___x_1898_, v___x_1894_);
return v___x_1899_;
}
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1900_ = lean_nat_sub(v_start_1885_, v_tailOff_1891_);
v___x_1901_ = lean_array_get_size(v_tail_1889_);
v___x_1902_ = lean_nat_dec_lt(v___x_1900_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_dec(v___x_1900_);
return v_init_1884_;
}
else
{
size_t v___x_1903_; size_t v___x_1904_; lean_object* v___x_1905_; 
v___x_1903_ = lean_usize_of_nat(v___x_1900_);
lean_dec(v___x_1900_);
v___x_1904_ = lean_usize_of_nat(v___x_1901_);
v___x_1905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1889_, v___x_1903_, v___x_1904_, v_init_1884_);
return v___x_1905_;
}
}
}
else
{
lean_object* v_root_1906_; lean_object* v_tail_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; 
v_root_1906_ = lean_ctor_get(v_t_1883_, 0);
v_tail_1907_ = lean_ctor_get(v_t_1883_, 1);
v___x_1908_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_root_1906_, v_init_1884_);
v___x_1909_ = lean_array_get_size(v_tail_1907_);
v___x_1910_ = lean_nat_dec_lt(v___x_1886_, v___x_1909_);
if (v___x_1910_ == 0)
{
return v___x_1908_;
}
else
{
size_t v___x_1911_; size_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = ((size_t)0ULL);
v___x_1912_ = lean_usize_of_nat(v___x_1909_);
v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_tail_1907_, v___x_1911_, v___x_1912_, v___x_1908_);
return v___x_1913_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg___boxed(lean_object* v_t_1914_, lean_object* v_init_1915_, lean_object* v_start_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1914_, v_init_1915_, v_start_1916_);
lean_dec(v_start_1916_);
lean_dec_ref(v_t_1914_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object* v_t_1918_){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = ((lean_object*)(l_Lean_PersistentArray_mkNewTail___redArg___closed__0));
v___x_1921_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1918_, v___x_1920_, v___x_1919_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___redArg___boxed(lean_object* v_t_1922_){
_start:
{
lean_object* v_res_1923_; 
v_res_1923_ = l_Lean_PersistentArray_toArray___redArg(v_t_1922_);
lean_dec_ref(v_t_1922_);
return v_res_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray(lean_object* v_00_u03b1_1924_, lean_object* v_t_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Lean_PersistentArray_toArray___redArg(v_t_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toArray___boxed(lean_object* v_00_u03b1_1927_, lean_object* v_t_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_PersistentArray_toArray(v_00_u03b1_1927_, v_t_1928_);
lean_dec_ref(v_t_1928_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(lean_object* v_00_u03b1_1930_, lean_object* v_t_1931_, lean_object* v_init_1932_, lean_object* v_start_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___redArg(v_t_1931_, v_init_1932_, v_start_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0___boxed(lean_object* v_00_u03b1_1935_, lean_object* v_t_1936_, lean_object* v_init_1937_, lean_object* v_start_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0(v_00_u03b1_1935_, v_t_1936_, v_init_1937_, v_start_1938_);
lean_dec(v_start_1938_);
lean_dec_ref(v_t_1936_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(lean_object* v_00_u03b1_1940_, lean_object* v_x_1941_, size_t v_x_1942_, size_t v_x_1943_, lean_object* v_x_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___redArg(v_x_1941_, v_x_1942_, v_x_1943_, v_x_1944_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_x_1950_){
_start:
{
size_t v_x_1236__boxed_1951_; size_t v_x_1237__boxed_1952_; lean_object* v_res_1953_; 
v_x_1236__boxed_1951_ = lean_unbox_usize(v_x_1948_);
lean_dec(v_x_1948_);
v_x_1237__boxed_1952_ = lean_unbox_usize(v_x_1949_);
lean_dec(v_x_1949_);
v_res_1953_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0(v_00_u03b1_1946_, v_x_1947_, v_x_1236__boxed_1951_, v_x_1237__boxed_1952_, v_x_1950_);
lean_dec_ref(v_x_1947_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(lean_object* v_00_u03b1_1954_, lean_object* v_as_1955_, size_t v_i_1956_, size_t v_stop_1957_, lean_object* v_b_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___redArg(v_as_1955_, v_i_1956_, v_stop_1957_, v_b_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1960_, lean_object* v_as_1961_, lean_object* v_i_1962_, lean_object* v_stop_1963_, lean_object* v_b_1964_){
_start:
{
size_t v_i_boxed_1965_; size_t v_stop_boxed_1966_; lean_object* v_res_1967_; 
v_i_boxed_1965_ = lean_unbox_usize(v_i_1962_);
lean_dec(v_i_1962_);
v_stop_boxed_1966_ = lean_unbox_usize(v_stop_1963_);
lean_dec(v_stop_1963_);
v_res_1967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__1(v_00_u03b1_1960_, v_as_1961_, v_i_boxed_1965_, v_stop_boxed_1966_, v_b_1964_);
lean_dec_ref(v_as_1961_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(lean_object* v_00_u03b1_1968_, lean_object* v_x_1969_, lean_object* v_x_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___redArg(v_x_1969_, v_x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__2(v_00_u03b1_1972_, v_x_1973_, v_x_1974_);
lean_dec_ref(v_x_1973_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1976_, lean_object* v_as_1977_, size_t v_i_1978_, size_t v_stop_1979_, lean_object* v_b_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___redArg(v_as_1977_, v_i_1978_, v_stop_1979_, v_b_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1982_, lean_object* v_as_1983_, lean_object* v_i_1984_, lean_object* v_stop_1985_, lean_object* v_b_1986_){
_start:
{
size_t v_i_boxed_1987_; size_t v_stop_boxed_1988_; lean_object* v_res_1989_; 
v_i_boxed_1987_ = lean_unbox_usize(v_i_1984_);
lean_dec(v_i_1984_);
v_stop_boxed_1988_ = lean_unbox_usize(v_stop_1985_);
lean_dec(v_stop_1985_);
v_res_1989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toArray_spec__0_spec__0_spec__1(v_00_u03b1_1982_, v_as_1983_, v_i_boxed_1987_, v_stop_boxed_1988_, v_b_1986_);
lean_dec_ref(v_as_1983_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(lean_object* v_as_1990_, size_t v_i_1991_, size_t v_stop_1992_, lean_object* v_b_1993_){
_start:
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_usize_dec_eq(v_i_1991_, v_stop_1992_);
if (v___x_1994_ == 0)
{
lean_object* v___x_1995_; lean_object* v___x_1996_; size_t v___x_1997_; size_t v___x_1998_; 
v___x_1995_ = lean_array_uget_borrowed(v_as_1990_, v_i_1991_);
lean_inc(v___x_1995_);
v___x_1996_ = l_Lean_PersistentArray_push___redArg(v_b_1993_, v___x_1995_);
v___x_1997_ = ((size_t)1ULL);
v___x_1998_ = lean_usize_add(v_i_1991_, v___x_1997_);
v_i_1991_ = v___x_1998_;
v_b_1993_ = v___x_1996_;
goto _start;
}
else
{
return v_b_1993_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg___boxed(lean_object* v_as_2000_, lean_object* v_i_2001_, lean_object* v_stop_2002_, lean_object* v_b_2003_){
_start:
{
size_t v_i_boxed_2004_; size_t v_stop_boxed_2005_; lean_object* v_res_2006_; 
v_i_boxed_2004_ = lean_unbox_usize(v_i_2001_);
lean_dec(v_i_2001_);
v_stop_boxed_2005_ = lean_unbox_usize(v_stop_2002_);
lean_dec(v_stop_2002_);
v_res_2006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2000_, v_i_boxed_2004_, v_stop_boxed_2005_, v_b_2003_);
lean_dec_ref(v_as_2000_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(lean_object* v_x_2007_, lean_object* v_x_2008_){
_start:
{
if (lean_obj_tag(v_x_2007_) == 0)
{
lean_object* v_cs_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_cs_2009_ = lean_ctor_get(v_x_2007_, 0);
v___x_2010_ = lean_unsigned_to_nat(0u);
v___x_2011_ = lean_array_get_size(v_cs_2009_);
v___x_2012_ = lean_nat_dec_lt(v___x_2010_, v___x_2011_);
if (v___x_2012_ == 0)
{
return v_x_2008_;
}
else
{
size_t v___x_2013_; size_t v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = ((size_t)0ULL);
v___x_2014_ = lean_usize_of_nat(v___x_2011_);
v___x_2015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2009_, v___x_2013_, v___x_2014_, v_x_2008_);
return v___x_2015_;
}
}
else
{
lean_object* v_vs_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v_vs_2016_ = lean_ctor_get(v_x_2007_, 0);
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = lean_array_get_size(v_vs_2016_);
v___x_2019_ = lean_nat_dec_lt(v___x_2017_, v___x_2018_);
if (v___x_2019_ == 0)
{
return v_x_2008_;
}
else
{
size_t v___x_2020_; size_t v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = ((size_t)0ULL);
v___x_2021_ = lean_usize_of_nat(v___x_2018_);
v___x_2022_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2016_, v___x_2020_, v___x_2021_, v_x_2008_);
return v___x_2022_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2023_, size_t v_i_2024_, size_t v_stop_2025_, lean_object* v_b_2026_){
_start:
{
uint8_t v___x_2027_; 
v___x_2027_ = lean_usize_dec_eq(v_i_2024_, v_stop_2025_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2029_; size_t v___x_2030_; size_t v___x_2031_; 
v___x_2028_ = lean_array_uget_borrowed(v_as_2023_, v_i_2024_);
v___x_2029_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v___x_2028_, v_b_2026_);
v___x_2030_ = ((size_t)1ULL);
v___x_2031_ = lean_usize_add(v_i_2024_, v___x_2030_);
v_i_2024_ = v___x_2031_;
v_b_2026_ = v___x_2029_;
goto _start;
}
else
{
return v_b_2026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2033_, lean_object* v_i_2034_, lean_object* v_stop_2035_, lean_object* v_b_2036_){
_start:
{
size_t v_i_boxed_2037_; size_t v_stop_boxed_2038_; lean_object* v_res_2039_; 
v_i_boxed_2037_ = lean_unbox_usize(v_i_2034_);
lean_dec(v_i_2034_);
v_stop_boxed_2038_ = lean_unbox_usize(v_stop_2035_);
lean_dec(v_stop_2035_);
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2033_, v_i_boxed_2037_, v_stop_boxed_2038_, v_b_2036_);
lean_dec_ref(v_as_2033_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg___boxed(lean_object* v_x_2040_, lean_object* v_x_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2040_, v_x_2041_);
lean_dec_ref(v_x_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(lean_object* v_x_2043_, size_t v_x_2044_, size_t v_x_2045_, lean_object* v_x_2046_){
_start:
{
if (lean_obj_tag(v_x_2043_) == 0)
{
lean_object* v_cs_2047_; lean_object* v___x_2048_; size_t v___x_2049_; lean_object* v_j_2050_; lean_object* v___x_2051_; size_t v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; size_t v___x_2055_; size_t v___x_2056_; size_t v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; uint8_t v___x_2062_; 
v_cs_2047_ = lean_ctor_get(v_x_2043_, 0);
v___x_2048_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_2049_ = lean_usize_shift_right(v_x_2044_, v_x_2045_);
v_j_2050_ = lean_usize_to_nat(v___x_2049_);
v___x_2051_ = lean_array_get_borrowed(v___x_2048_, v_cs_2047_, v_j_2050_);
v___x_2052_ = ((size_t)1ULL);
v___x_2053_ = lean_usize_shift_left(v___x_2052_, v_x_2045_);
v___x_2054_ = lean_usize_sub(v___x_2053_, v___x_2052_);
v___x_2055_ = lean_usize_land(v_x_2044_, v___x_2054_);
v___x_2056_ = ((size_t)5ULL);
v___x_2057_ = lean_usize_sub(v_x_2045_, v___x_2056_);
v___x_2058_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v___x_2051_, v___x_2055_, v___x_2057_, v_x_2046_);
v___x_2059_ = lean_unsigned_to_nat(1u);
v___x_2060_ = lean_nat_add(v_j_2050_, v___x_2059_);
lean_dec(v_j_2050_);
v___x_2061_ = lean_array_get_size(v_cs_2047_);
v___x_2062_ = lean_nat_dec_lt(v___x_2060_, v___x_2061_);
if (v___x_2062_ == 0)
{
lean_dec(v___x_2060_);
return v___x_2058_;
}
else
{
size_t v___x_2063_; size_t v___x_2064_; lean_object* v___x_2065_; 
v___x_2063_ = lean_usize_of_nat(v___x_2060_);
lean_dec(v___x_2060_);
v___x_2064_ = lean_usize_of_nat(v___x_2061_);
v___x_2065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_cs_2047_, v___x_2063_, v___x_2064_, v___x_2058_);
return v___x_2065_;
}
}
else
{
lean_object* v_vs_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_vs_2066_ = lean_ctor_get(v_x_2043_, 0);
v___x_2067_ = lean_usize_to_nat(v_x_2044_);
v___x_2068_ = lean_array_get_size(v_vs_2066_);
v___x_2069_ = lean_nat_dec_lt(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_dec(v___x_2067_);
return v_x_2046_;
}
else
{
size_t v___x_2070_; size_t v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_usize_of_nat(v___x_2067_);
lean_dec(v___x_2067_);
v___x_2071_ = lean_usize_of_nat(v___x_2068_);
v___x_2072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_vs_2066_, v___x_2070_, v___x_2071_, v_x_2046_);
return v___x_2072_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg___boxed(lean_object* v_x_2073_, lean_object* v_x_2074_, lean_object* v_x_2075_, lean_object* v_x_2076_){
_start:
{
size_t v_x_1123__boxed_2077_; size_t v_x_1124__boxed_2078_; lean_object* v_res_2079_; 
v_x_1123__boxed_2077_ = lean_unbox_usize(v_x_2074_);
lean_dec(v_x_2074_);
v_x_1124__boxed_2078_ = lean_unbox_usize(v_x_2075_);
lean_dec(v_x_2075_);
v_res_2079_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2073_, v_x_1123__boxed_2077_, v_x_1124__boxed_2078_, v_x_2076_);
lean_dec_ref(v_x_2073_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(lean_object* v_t_2080_, lean_object* v_init_2081_, lean_object* v_start_2082_){
_start:
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = lean_nat_dec_eq(v_start_2082_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_object* v_root_2085_; lean_object* v_tail_2086_; size_t v_shift_2087_; lean_object* v_tailOff_2088_; uint8_t v___x_2089_; 
v_root_2085_ = lean_ctor_get(v_t_2080_, 0);
v_tail_2086_ = lean_ctor_get(v_t_2080_, 1);
v_shift_2087_ = lean_ctor_get_usize(v_t_2080_, 4);
v_tailOff_2088_ = lean_ctor_get(v_t_2080_, 3);
v___x_2089_ = lean_nat_dec_le(v_tailOff_2088_, v_start_2082_);
if (v___x_2089_ == 0)
{
size_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v___x_2090_ = lean_usize_of_nat(v_start_2082_);
v___x_2091_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_root_2085_, v___x_2090_, v_shift_2087_, v_init_2081_);
v___x_2092_ = lean_array_get_size(v_tail_2086_);
v___x_2093_ = lean_nat_dec_lt(v___x_2083_, v___x_2092_);
if (v___x_2093_ == 0)
{
return v___x_2091_;
}
else
{
size_t v___x_2094_; size_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2094_ = ((size_t)0ULL);
v___x_2095_ = lean_usize_of_nat(v___x_2092_);
v___x_2096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2086_, v___x_2094_, v___x_2095_, v___x_2091_);
return v___x_2096_;
}
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2097_ = lean_nat_sub(v_start_2082_, v_tailOff_2088_);
v___x_2098_ = lean_array_get_size(v_tail_2086_);
v___x_2099_ = lean_nat_dec_lt(v___x_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
lean_dec(v___x_2097_);
return v_init_2081_;
}
else
{
size_t v___x_2100_; size_t v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = lean_usize_of_nat(v___x_2097_);
lean_dec(v___x_2097_);
v___x_2101_ = lean_usize_of_nat(v___x_2098_);
v___x_2102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2086_, v___x_2100_, v___x_2101_, v_init_2081_);
return v___x_2102_;
}
}
}
else
{
lean_object* v_root_2103_; lean_object* v_tail_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v_root_2103_ = lean_ctor_get(v_t_2080_, 0);
v_tail_2104_ = lean_ctor_get(v_t_2080_, 1);
v___x_2105_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_root_2103_, v_init_2081_);
v___x_2106_ = lean_array_get_size(v_tail_2104_);
v___x_2107_ = lean_nat_dec_lt(v___x_2083_, v___x_2106_);
if (v___x_2107_ == 0)
{
return v___x_2105_;
}
else
{
size_t v___x_2108_; size_t v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = ((size_t)0ULL);
v___x_2109_ = lean_usize_of_nat(v___x_2106_);
v___x_2110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_tail_2104_, v___x_2108_, v___x_2109_, v___x_2105_);
return v___x_2110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg___boxed(lean_object* v_t_2111_, lean_object* v_init_2112_, lean_object* v_start_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2111_, v_init_2112_, v_start_2113_);
lean_dec(v_start_2113_);
lean_dec_ref(v_t_2111_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg(lean_object* v_t_u2081_2115_, lean_object* v_t_u2082_2116_){
_start:
{
uint8_t v___x_2117_; 
v___x_2117_ = l_Lean_PersistentArray_isEmpty___redArg(v_t_u2081_2115_);
if (v___x_2117_ == 0)
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_u2082_2116_, v_t_u2081_2115_, v___x_2118_);
return v___x_2119_;
}
else
{
lean_dec_ref(v_t_u2081_2115_);
lean_inc_ref(v_t_u2082_2116_);
return v_t_u2082_2116_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___redArg___boxed(lean_object* v_t_u2081_2120_, lean_object* v_t_u2082_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2120_, v_t_u2082_2121_);
lean_dec_ref(v_t_u2082_2121_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append(lean_object* v_00_u03b1_2123_, lean_object* v_t_u2081_2124_, lean_object* v_t_u2082_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_PersistentArray_append___redArg(v_t_u2081_2124_, v_t_u2082_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_append___boxed(lean_object* v_00_u03b1_2127_, lean_object* v_t_u2081_2128_, lean_object* v_t_u2082_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_PersistentArray_append(v_00_u03b1_2127_, v_t_u2081_2128_, v_t_u2082_2129_);
lean_dec_ref(v_t_u2082_2129_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(lean_object* v_00_u03b1_2131_, lean_object* v_t_2132_, lean_object* v_init_2133_, lean_object* v_start_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___redArg(v_t_2132_, v_init_2133_, v_start_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0___boxed(lean_object* v_00_u03b1_2136_, lean_object* v_t_2137_, lean_object* v_init_2138_, lean_object* v_start_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0(v_00_u03b1_2136_, v_t_2137_, v_init_2138_, v_start_2139_);
lean_dec(v_start_2139_);
lean_dec_ref(v_t_2137_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(lean_object* v_00_u03b1_2141_, lean_object* v_x_2142_, size_t v_x_2143_, size_t v_x_2144_, lean_object* v_x_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___redArg(v_x_2142_, v_x_2143_, v_x_2144_, v_x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_, lean_object* v_x_2151_){
_start:
{
size_t v_x_1239__boxed_2152_; size_t v_x_1240__boxed_2153_; lean_object* v_res_2154_; 
v_x_1239__boxed_2152_ = lean_unbox_usize(v_x_2149_);
lean_dec(v_x_2149_);
v_x_1240__boxed_2153_ = lean_unbox_usize(v_x_2150_);
lean_dec(v_x_2150_);
v_res_2154_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0(v_00_u03b1_2147_, v_x_2148_, v_x_1239__boxed_2152_, v_x_1240__boxed_2153_, v_x_2151_);
lean_dec_ref(v_x_2148_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(lean_object* v_00_u03b1_2155_, lean_object* v_as_2156_, size_t v_i_2157_, size_t v_stop_2158_, lean_object* v_b_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_as_2156_, v_i_2157_, v_stop_2158_, v_b_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2161_, lean_object* v_as_2162_, lean_object* v_i_2163_, lean_object* v_stop_2164_, lean_object* v_b_2165_){
_start:
{
size_t v_i_boxed_2166_; size_t v_stop_boxed_2167_; lean_object* v_res_2168_; 
v_i_boxed_2166_ = lean_unbox_usize(v_i_2163_);
lean_dec(v_i_2163_);
v_stop_boxed_2167_ = lean_unbox_usize(v_stop_2164_);
lean_dec(v_stop_2164_);
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1(v_00_u03b1_2161_, v_as_2162_, v_i_boxed_2166_, v_stop_boxed_2167_, v_b_2165_);
lean_dec_ref(v_as_2162_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(lean_object* v_00_u03b1_2169_, lean_object* v_x_2170_, lean_object* v_x_2171_){
_start:
{
lean_object* v___x_2172_; 
v___x_2172_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___redArg(v_x_2170_, v_x_2171_);
return v___x_2172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__2(v_00_u03b1_2173_, v_x_2174_, v_x_2175_);
lean_dec_ref(v_x_2174_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2177_, lean_object* v_as_2178_, size_t v_i_2179_, size_t v_stop_2180_, lean_object* v_b_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___redArg(v_as_2178_, v_i_2179_, v_stop_2180_, v_b_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2183_, lean_object* v_as_2184_, lean_object* v_i_2185_, lean_object* v_stop_2186_, lean_object* v_b_2187_){
_start:
{
size_t v_i_boxed_2188_; size_t v_stop_boxed_2189_; lean_object* v_res_2190_; 
v_i_boxed_2188_ = lean_unbox_usize(v_i_2185_);
lean_dec(v_i_2185_);
v_stop_boxed_2189_ = lean_unbox_usize(v_stop_2186_);
lean_dec(v_stop_2186_);
v_res_2190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__0_spec__1(v_00_u03b1_2183_, v_as_2184_, v_i_boxed_2188_, v_stop_boxed_2189_, v_b_2187_);
lean_dec_ref(v_as_2184_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_instAppend(lean_object* v_00_u03b1_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = ((lean_object*)(l_Lean_PersistentArray_instAppend___closed__0));
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg___lam__0(lean_object* v_f_2194_, lean_object* v_x_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = lean_apply_1(v_f_2194_, v_x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f___redArg(lean_object* v_t_2197_, lean_object* v_f_2198_){
_start:
{
lean_object* v___f_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___f_2199_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2199_, 0, v_f_2198_);
v___x_2200_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2201_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2200_, v_t_2197_, v___f_2199_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSome_x3f(lean_object* v_00_u03b1_2202_, lean_object* v_00_u03b2_2203_, lean_object* v_t_2204_, lean_object* v_f_2205_){
_start:
{
lean_object* v___f_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___f_2206_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2206_, 0, v_f_2205_);
v___x_2207_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2208_ = l_Lean_PersistentArray_findSomeM_x3f___redArg(v___x_2207_, v_t_2204_, v___f_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f___redArg(lean_object* v_t_2209_, lean_object* v_f_2210_){
_start:
{
lean_object* v___f_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___f_2211_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2211_, 0, v_f_2210_);
v___x_2212_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2213_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2212_, v_t_2209_, v___f_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRev_x3f(lean_object* v_00_u03b1_2214_, lean_object* v_00_u03b2_2215_, lean_object* v_t_2216_, lean_object* v_f_2217_){
_start:
{
lean_object* v___f_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___f_2218_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_findSome_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2218_, 0, v_f_2217_);
v___x_2219_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2220_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2219_, v_t_2216_, v___f_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(lean_object* v_as_2221_, size_t v_i_2222_, size_t v_stop_2223_, lean_object* v_b_2224_){
_start:
{
uint8_t v___x_2225_; 
v___x_2225_ = lean_usize_dec_eq(v_i_2222_, v_stop_2223_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; lean_object* v___x_2227_; size_t v___x_2228_; size_t v___x_2229_; 
v___x_2226_ = lean_array_uget_borrowed(v_as_2221_, v_i_2222_);
lean_inc(v___x_2226_);
v___x_2227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v_b_2224_);
v___x_2228_ = ((size_t)1ULL);
v___x_2229_ = lean_usize_add(v_i_2222_, v___x_2228_);
v_i_2222_ = v___x_2229_;
v_b_2224_ = v___x_2227_;
goto _start;
}
else
{
return v_b_2224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg___boxed(lean_object* v_as_2231_, lean_object* v_i_2232_, lean_object* v_stop_2233_, lean_object* v_b_2234_){
_start:
{
size_t v_i_boxed_2235_; size_t v_stop_boxed_2236_; lean_object* v_res_2237_; 
v_i_boxed_2235_ = lean_unbox_usize(v_i_2232_);
lean_dec(v_i_2232_);
v_stop_boxed_2236_ = lean_unbox_usize(v_stop_2233_);
lean_dec(v_stop_2233_);
v_res_2237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2231_, v_i_boxed_2235_, v_stop_boxed_2236_, v_b_2234_);
lean_dec_ref(v_as_2231_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
if (lean_obj_tag(v_x_2238_) == 0)
{
lean_object* v_cs_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; uint8_t v___x_2243_; 
v_cs_2240_ = lean_ctor_get(v_x_2238_, 0);
v___x_2241_ = lean_unsigned_to_nat(0u);
v___x_2242_ = lean_array_get_size(v_cs_2240_);
v___x_2243_ = lean_nat_dec_lt(v___x_2241_, v___x_2242_);
if (v___x_2243_ == 0)
{
return v_x_2239_;
}
else
{
size_t v___x_2244_; size_t v___x_2245_; lean_object* v___x_2246_; 
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = lean_usize_of_nat(v___x_2242_);
v___x_2246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2240_, v___x_2244_, v___x_2245_, v_x_2239_);
return v___x_2246_;
}
}
else
{
lean_object* v_vs_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; 
v_vs_2247_ = lean_ctor_get(v_x_2238_, 0);
v___x_2248_ = lean_unsigned_to_nat(0u);
v___x_2249_ = lean_array_get_size(v_vs_2247_);
v___x_2250_ = lean_nat_dec_lt(v___x_2248_, v___x_2249_);
if (v___x_2250_ == 0)
{
return v_x_2239_;
}
else
{
size_t v___x_2251_; size_t v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = ((size_t)0ULL);
v___x_2252_ = lean_usize_of_nat(v___x_2249_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2247_, v___x_2251_, v___x_2252_, v_x_2239_);
return v___x_2253_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(lean_object* v_as_2254_, size_t v_i_2255_, size_t v_stop_2256_, lean_object* v_b_2257_){
_start:
{
uint8_t v___x_2258_; 
v___x_2258_ = lean_usize_dec_eq(v_i_2255_, v_stop_2256_);
if (v___x_2258_ == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2260_; size_t v___x_2261_; size_t v___x_2262_; 
v___x_2259_ = lean_array_uget_borrowed(v_as_2254_, v_i_2255_);
v___x_2260_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v___x_2259_, v_b_2257_);
v___x_2261_ = ((size_t)1ULL);
v___x_2262_ = lean_usize_add(v_i_2255_, v___x_2261_);
v_i_2255_ = v___x_2262_;
v_b_2257_ = v___x_2260_;
goto _start;
}
else
{
return v_b_2257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_as_2264_, lean_object* v_i_2265_, lean_object* v_stop_2266_, lean_object* v_b_2267_){
_start:
{
size_t v_i_boxed_2268_; size_t v_stop_boxed_2269_; lean_object* v_res_2270_; 
v_i_boxed_2268_ = lean_unbox_usize(v_i_2265_);
lean_dec(v_i_2265_);
v_stop_boxed_2269_ = lean_unbox_usize(v_stop_2266_);
lean_dec(v_stop_2266_);
v_res_2270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2264_, v_i_boxed_2268_, v_stop_boxed_2269_, v_b_2267_);
lean_dec_ref(v_as_2264_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg___boxed(lean_object* v_x_2271_, lean_object* v_x_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2271_, v_x_2272_);
lean_dec_ref(v_x_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(lean_object* v_x_2274_, size_t v_x_2275_, size_t v_x_2276_, lean_object* v_x_2277_){
_start:
{
if (lean_obj_tag(v_x_2274_) == 0)
{
lean_object* v_cs_2278_; lean_object* v___x_2279_; size_t v___x_2280_; lean_object* v_j_2281_; lean_object* v___x_2282_; size_t v___x_2283_; size_t v___x_2284_; size_t v___x_2285_; size_t v___x_2286_; size_t v___x_2287_; size_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; 
v_cs_2278_ = lean_ctor_get(v_x_2274_, 0);
v___x_2279_ = lean_obj_once(&l_Lean_instInhabitedPersistentArrayNode___closed__0, &l_Lean_instInhabitedPersistentArrayNode___closed__0_once, _init_l_Lean_instInhabitedPersistentArrayNode___closed__0);
v___x_2280_ = lean_usize_shift_right(v_x_2275_, v_x_2276_);
v_j_2281_ = lean_usize_to_nat(v___x_2280_);
v___x_2282_ = lean_array_get_borrowed(v___x_2279_, v_cs_2278_, v_j_2281_);
v___x_2283_ = ((size_t)1ULL);
v___x_2284_ = lean_usize_shift_left(v___x_2283_, v_x_2276_);
v___x_2285_ = lean_usize_sub(v___x_2284_, v___x_2283_);
v___x_2286_ = lean_usize_land(v_x_2275_, v___x_2285_);
v___x_2287_ = ((size_t)5ULL);
v___x_2288_ = lean_usize_sub(v_x_2276_, v___x_2287_);
v___x_2289_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v___x_2282_, v___x_2286_, v___x_2288_, v_x_2277_);
v___x_2290_ = lean_unsigned_to_nat(1u);
v___x_2291_ = lean_nat_add(v_j_2281_, v___x_2290_);
lean_dec(v_j_2281_);
v___x_2292_ = lean_array_get_size(v_cs_2278_);
v___x_2293_ = lean_nat_dec_lt(v___x_2291_, v___x_2292_);
if (v___x_2293_ == 0)
{
lean_dec(v___x_2291_);
return v___x_2289_;
}
else
{
size_t v___x_2294_; size_t v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_usize_of_nat(v___x_2291_);
lean_dec(v___x_2291_);
v___x_2295_ = lean_usize_of_nat(v___x_2292_);
v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_cs_2278_, v___x_2294_, v___x_2295_, v___x_2289_);
return v___x_2296_;
}
}
else
{
lean_object* v_vs_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; uint8_t v___x_2300_; 
v_vs_2297_ = lean_ctor_get(v_x_2274_, 0);
v___x_2298_ = lean_usize_to_nat(v_x_2275_);
v___x_2299_ = lean_array_get_size(v_vs_2297_);
v___x_2300_ = lean_nat_dec_lt(v___x_2298_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_dec(v___x_2298_);
return v_x_2277_;
}
else
{
size_t v___x_2301_; size_t v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = lean_usize_of_nat(v___x_2298_);
lean_dec(v___x_2298_);
v___x_2302_ = lean_usize_of_nat(v___x_2299_);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_vs_2297_, v___x_2301_, v___x_2302_, v_x_2277_);
return v___x_2303_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg___boxed(lean_object* v_x_2304_, lean_object* v_x_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_){
_start:
{
size_t v_x_1118__boxed_2308_; size_t v_x_1119__boxed_2309_; lean_object* v_res_2310_; 
v_x_1118__boxed_2308_ = lean_unbox_usize(v_x_2305_);
lean_dec(v_x_2305_);
v_x_1119__boxed_2309_ = lean_unbox_usize(v_x_2306_);
lean_dec(v_x_2306_);
v_res_2310_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2304_, v_x_1118__boxed_2308_, v_x_1119__boxed_2309_, v_x_2307_);
lean_dec_ref(v_x_2304_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(lean_object* v_t_2311_, lean_object* v_init_2312_, lean_object* v_start_2313_){
_start:
{
lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = lean_unsigned_to_nat(0u);
v___x_2315_ = lean_nat_dec_eq(v_start_2313_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v_root_2316_; lean_object* v_tail_2317_; size_t v_shift_2318_; lean_object* v_tailOff_2319_; uint8_t v___x_2320_; 
v_root_2316_ = lean_ctor_get(v_t_2311_, 0);
v_tail_2317_ = lean_ctor_get(v_t_2311_, 1);
v_shift_2318_ = lean_ctor_get_usize(v_t_2311_, 4);
v_tailOff_2319_ = lean_ctor_get(v_t_2311_, 3);
v___x_2320_ = lean_nat_dec_le(v_tailOff_2319_, v_start_2313_);
if (v___x_2320_ == 0)
{
size_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2321_ = lean_usize_of_nat(v_start_2313_);
v___x_2322_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_root_2316_, v___x_2321_, v_shift_2318_, v_init_2312_);
v___x_2323_ = lean_array_get_size(v_tail_2317_);
v___x_2324_ = lean_nat_dec_lt(v___x_2314_, v___x_2323_);
if (v___x_2324_ == 0)
{
return v___x_2322_;
}
else
{
size_t v___x_2325_; size_t v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = ((size_t)0ULL);
v___x_2326_ = lean_usize_of_nat(v___x_2323_);
v___x_2327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2317_, v___x_2325_, v___x_2326_, v___x_2322_);
return v___x_2327_;
}
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2328_ = lean_nat_sub(v_start_2313_, v_tailOff_2319_);
v___x_2329_ = lean_array_get_size(v_tail_2317_);
v___x_2330_ = lean_nat_dec_lt(v___x_2328_, v___x_2329_);
if (v___x_2330_ == 0)
{
lean_dec(v___x_2328_);
return v_init_2312_;
}
else
{
size_t v___x_2331_; size_t v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = lean_usize_of_nat(v___x_2328_);
lean_dec(v___x_2328_);
v___x_2332_ = lean_usize_of_nat(v___x_2329_);
v___x_2333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2317_, v___x_2331_, v___x_2332_, v_init_2312_);
return v___x_2333_;
}
}
}
else
{
lean_object* v_root_2334_; lean_object* v_tail_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; uint8_t v___x_2338_; 
v_root_2334_ = lean_ctor_get(v_t_2311_, 0);
v_tail_2335_ = lean_ctor_get(v_t_2311_, 1);
v___x_2336_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_root_2334_, v_init_2312_);
v___x_2337_ = lean_array_get_size(v_tail_2335_);
v___x_2338_ = lean_nat_dec_lt(v___x_2314_, v___x_2337_);
if (v___x_2338_ == 0)
{
return v___x_2336_;
}
else
{
size_t v___x_2339_; size_t v___x_2340_; lean_object* v___x_2341_; 
v___x_2339_ = ((size_t)0ULL);
v___x_2340_ = lean_usize_of_nat(v___x_2337_);
v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_tail_2335_, v___x_2339_, v___x_2340_, v___x_2336_);
return v___x_2341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg___boxed(lean_object* v_t_2342_, lean_object* v_init_2343_, lean_object* v_start_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2342_, v_init_2343_, v_start_2344_);
lean_dec(v_start_2344_);
lean_dec_ref(v_t_2342_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg(lean_object* v_t_2346_){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2347_ = lean_box(0);
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2346_, v___x_2347_, v___x_2348_);
v___x_2350_ = l_List_reverse___redArg(v___x_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___redArg___boxed(lean_object* v_t_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_PersistentArray_toList___redArg(v_t_2351_);
lean_dec_ref(v_t_2351_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList(lean_object* v_00_u03b1_2353_, lean_object* v_t_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_PersistentArray_toList___redArg(v_t_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_toList___boxed(lean_object* v_00_u03b1_2356_, lean_object* v_t_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_PersistentArray_toList(v_00_u03b1_2356_, v_t_2357_);
lean_dec_ref(v_t_2357_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(lean_object* v_00_u03b1_2359_, lean_object* v_t_2360_, lean_object* v_init_2361_, lean_object* v_start_2362_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___redArg(v_t_2360_, v_init_2361_, v_start_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0___boxed(lean_object* v_00_u03b1_2364_, lean_object* v_t_2365_, lean_object* v_init_2366_, lean_object* v_start_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l_Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0(v_00_u03b1_2364_, v_t_2365_, v_init_2366_, v_start_2367_);
lean_dec(v_start_2367_);
lean_dec_ref(v_t_2365_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(lean_object* v_00_u03b1_2369_, lean_object* v_x_2370_, size_t v_x_2371_, size_t v_x_2372_, lean_object* v_x_2373_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___redArg(v_x_2370_, v_x_2371_, v_x_2372_, v_x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2375_, lean_object* v_x_2376_, lean_object* v_x_2377_, lean_object* v_x_2378_, lean_object* v_x_2379_){
_start:
{
size_t v_x_1236__boxed_2380_; size_t v_x_1237__boxed_2381_; lean_object* v_res_2382_; 
v_x_1236__boxed_2380_ = lean_unbox_usize(v_x_2377_);
lean_dec(v_x_2377_);
v_x_1237__boxed_2381_ = lean_unbox_usize(v_x_2378_);
lean_dec(v_x_2378_);
v_res_2382_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0(v_00_u03b1_2375_, v_x_2376_, v_x_1236__boxed_2380_, v_x_1237__boxed_2381_, v_x_2379_);
lean_dec_ref(v_x_2376_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(lean_object* v_00_u03b1_2383_, lean_object* v_as_2384_, size_t v_i_2385_, size_t v_stop_2386_, lean_object* v_b_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___redArg(v_as_2384_, v_i_2385_, v_stop_2386_, v_b_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2389_, lean_object* v_as_2390_, lean_object* v_i_2391_, lean_object* v_stop_2392_, lean_object* v_b_2393_){
_start:
{
size_t v_i_boxed_2394_; size_t v_stop_boxed_2395_; lean_object* v_res_2396_; 
v_i_boxed_2394_ = lean_unbox_usize(v_i_2391_);
lean_dec(v_i_2391_);
v_stop_boxed_2395_ = lean_unbox_usize(v_stop_2392_);
lean_dec(v_stop_2392_);
v_res_2396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__1(v_00_u03b1_2389_, v_as_2390_, v_i_boxed_2394_, v_stop_boxed_2395_, v_b_2393_);
lean_dec_ref(v_as_2390_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(lean_object* v_00_u03b1_2397_, lean_object* v_x_2398_, lean_object* v_x_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___redArg(v_x_2398_, v_x_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2401_, lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__2(v_00_u03b1_2401_, v_x_2402_, v_x_2403_);
lean_dec_ref(v_x_2402_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2405_, lean_object* v_as_2406_, size_t v_i_2407_, size_t v_stop_2408_, lean_object* v_b_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___redArg(v_as_2406_, v_i_2407_, v_stop_2408_, v_b_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2411_, lean_object* v_as_2412_, lean_object* v_i_2413_, lean_object* v_stop_2414_, lean_object* v_b_2415_){
_start:
{
size_t v_i_boxed_2416_; size_t v_stop_boxed_2417_; lean_object* v_res_2418_; 
v_i_boxed_2416_ = lean_unbox_usize(v_i_2413_);
lean_dec(v_i_2413_);
v_stop_boxed_2417_ = lean_unbox_usize(v_stop_2414_);
lean_dec(v_stop_2414_);
v_res_2418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_toList_spec__0_spec__0_spec__1(v_00_u03b1_2411_, v_as_2412_, v_i_boxed_2416_, v_stop_boxed_2417_, v_b_2415_);
lean_dec_ref(v_as_2412_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg(lean_object* v_inst_2419_, lean_object* v_p_2420_, lean_object* v_x_2421_){
_start:
{
if (lean_obj_tag(v_x_2421_) == 0)
{
lean_object* v_toApplicative_2422_; lean_object* v_cs_2423_; lean_object* v_toPure_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v_toApplicative_2422_ = lean_ctor_get(v_inst_2419_, 0);
v_cs_2423_ = lean_ctor_get(v_x_2421_, 0);
lean_inc_ref(v_cs_2423_);
lean_dec_ref_known(v_x_2421_, 1);
v_toPure_2424_ = lean_ctor_get(v_toApplicative_2422_, 1);
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = lean_array_get_size(v_cs_2423_);
v___x_2427_ = lean_nat_dec_lt(v___x_2425_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
lean_inc(v_toPure_2424_);
lean_dec_ref(v_cs_2423_);
lean_dec(v_p_2420_);
lean_dec_ref(v_inst_2419_);
v___x_2428_ = lean_box(v___x_2427_);
v___x_2429_ = lean_apply_2(v_toPure_2424_, lean_box(0), v___x_2428_);
return v___x_2429_;
}
else
{
if (v___x_2427_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
lean_inc(v_toPure_2424_);
lean_dec_ref(v_cs_2423_);
lean_dec(v_p_2420_);
lean_dec_ref(v_inst_2419_);
v___x_2430_ = lean_box(v___x_2427_);
v___x_2431_ = lean_apply_2(v_toPure_2424_, lean_box(0), v___x_2430_);
return v___x_2431_;
}
else
{
lean_object* v___f_2432_; size_t v___x_2433_; size_t v___x_2434_; lean_object* v___x_2435_; 
lean_inc_ref(v_inst_2419_);
v___f_2432_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyMAux___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2432_, 0, v_inst_2419_);
lean_closure_set(v___f_2432_, 1, v_p_2420_);
v___x_2433_ = ((size_t)0ULL);
v___x_2434_ = lean_usize_of_nat(v___x_2426_);
v___x_2435_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2419_, v___f_2432_, v_cs_2423_, v___x_2433_, v___x_2434_);
return v___x_2435_;
}
}
}
else
{
lean_object* v_toApplicative_2436_; lean_object* v_vs_2437_; lean_object* v_toPure_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v_toApplicative_2436_ = lean_ctor_get(v_inst_2419_, 0);
v_vs_2437_ = lean_ctor_get(v_x_2421_, 0);
lean_inc_ref(v_vs_2437_);
lean_dec_ref_known(v_x_2421_, 1);
v_toPure_2438_ = lean_ctor_get(v_toApplicative_2436_, 1);
v___x_2439_ = lean_unsigned_to_nat(0u);
v___x_2440_ = lean_array_get_size(v_vs_2437_);
v___x_2441_ = lean_nat_dec_lt(v___x_2439_, v___x_2440_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
lean_inc(v_toPure_2438_);
lean_dec_ref(v_vs_2437_);
lean_dec(v_p_2420_);
lean_dec_ref(v_inst_2419_);
v___x_2442_ = lean_box(v___x_2441_);
v___x_2443_ = lean_apply_2(v_toPure_2438_, lean_box(0), v___x_2442_);
return v___x_2443_;
}
else
{
if (v___x_2441_ == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
lean_inc(v_toPure_2438_);
lean_dec_ref(v_vs_2437_);
lean_dec(v_p_2420_);
lean_dec_ref(v_inst_2419_);
v___x_2444_ = lean_box(v___x_2441_);
v___x_2445_ = lean_apply_2(v_toPure_2438_, lean_box(0), v___x_2444_);
return v___x_2445_;
}
else
{
size_t v___x_2446_; size_t v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = ((size_t)0ULL);
v___x_2447_ = lean_usize_of_nat(v___x_2440_);
v___x_2448_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2419_, v_p_2420_, v_vs_2437_, v___x_2446_, v___x_2447_);
return v___x_2448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___redArg___lam__0(lean_object* v_inst_2449_, lean_object* v_p_2450_, lean_object* v_c_2451_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2449_, v_p_2450_, v_c_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux(lean_object* v_00_u03b1_2453_, lean_object* v_m_2454_, lean_object* v_inst_2455_, lean_object* v_p_2456_, lean_object* v_x_2457_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2455_, v_p_2456_, v_x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0(lean_object* v_tail_2459_, lean_object* v_toPure_2460_, lean_object* v_inst_2461_, lean_object* v_p_2462_, uint8_t v_b_2463_){
_start:
{
if (v_b_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2464_ = lean_unsigned_to_nat(0u);
v___x_2465_ = lean_array_get_size(v_tail_2459_);
v___x_2466_ = lean_nat_dec_lt(v___x_2464_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_dec(v_p_2462_);
lean_dec_ref(v_inst_2461_);
lean_dec_ref(v_tail_2459_);
v___x_2467_ = lean_box(v___x_2466_);
v___x_2468_ = lean_apply_2(v_toPure_2460_, lean_box(0), v___x_2467_);
return v___x_2468_;
}
else
{
if (v___x_2466_ == 0)
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
lean_dec(v_p_2462_);
lean_dec_ref(v_inst_2461_);
lean_dec_ref(v_tail_2459_);
v___x_2469_ = lean_box(v___x_2466_);
v___x_2470_ = lean_apply_2(v_toPure_2460_, lean_box(0), v___x_2469_);
return v___x_2470_;
}
else
{
size_t v___x_2471_; size_t v___x_2472_; lean_object* v___x_2473_; 
lean_dec(v_toPure_2460_);
v___x_2471_ = ((size_t)0ULL);
v___x_2472_ = lean_usize_of_nat(v___x_2465_);
v___x_2473_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(lean_box(0), lean_box(0), v_inst_2461_, v_p_2462_, v_tail_2459_, v___x_2471_, v___x_2472_);
return v___x_2473_;
}
}
}
else
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
lean_dec(v_p_2462_);
lean_dec_ref(v_inst_2461_);
lean_dec_ref(v_tail_2459_);
v___x_2474_ = lean_box(v_b_2463_);
v___x_2475_ = lean_apply_2(v_toPure_2460_, lean_box(0), v___x_2474_);
return v___x_2475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg___lam__0___boxed(lean_object* v_tail_2476_, lean_object* v_toPure_2477_, lean_object* v_inst_2478_, lean_object* v_p_2479_, lean_object* v_b_2480_){
_start:
{
uint8_t v_b_boxed_2481_; lean_object* v_res_2482_; 
v_b_boxed_2481_ = lean_unbox(v_b_2480_);
v_res_2482_ = l_Lean_PersistentArray_anyM___redArg___lam__0(v_tail_2476_, v_toPure_2477_, v_inst_2478_, v_p_2479_, v_b_boxed_2481_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___redArg(lean_object* v_inst_2483_, lean_object* v_t_2484_, lean_object* v_p_2485_){
_start:
{
lean_object* v_toApplicative_2486_; lean_object* v_toBind_2487_; lean_object* v_root_2488_; lean_object* v_tail_2489_; lean_object* v_toPure_2490_; lean_object* v___x_2491_; lean_object* v___f_2492_; lean_object* v___x_2493_; 
v_toApplicative_2486_ = lean_ctor_get(v_inst_2483_, 0);
v_toBind_2487_ = lean_ctor_get(v_inst_2483_, 1);
lean_inc(v_toBind_2487_);
v_root_2488_ = lean_ctor_get(v_t_2484_, 0);
lean_inc_ref(v_root_2488_);
v_tail_2489_ = lean_ctor_get(v_t_2484_, 1);
lean_inc_ref(v_tail_2489_);
lean_dec_ref(v_t_2484_);
v_toPure_2490_ = lean_ctor_get(v_toApplicative_2486_, 1);
lean_inc(v_toPure_2490_);
lean_inc(v_p_2485_);
lean_inc_ref(v_inst_2483_);
v___x_2491_ = l_Lean_PersistentArray_anyMAux___redArg(v_inst_2483_, v_p_2485_, v_root_2488_);
v___f_2492_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_anyM___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2492_, 0, v_tail_2489_);
lean_closure_set(v___f_2492_, 1, v_toPure_2490_);
lean_closure_set(v___f_2492_, 2, v_inst_2483_);
lean_closure_set(v___f_2492_, 3, v_p_2485_);
v___x_2493_ = lean_apply_4(v_toBind_2487_, lean_box(0), lean_box(0), v___x_2491_, v___f_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM(lean_object* v_00_u03b1_2494_, lean_object* v_m_2495_, lean_object* v_inst_2496_, lean_object* v_t_2497_, lean_object* v_p_2498_){
_start:
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2496_, v_t_2497_, v_p_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0(lean_object* v_toPure_2500_, uint8_t v_b_2501_){
_start:
{
if (v_b_2501_ == 0)
{
uint8_t v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = 1;
v___x_2503_ = lean_box(v___x_2502_);
v___x_2504_ = lean_apply_2(v_toPure_2500_, lean_box(0), v___x_2503_);
return v___x_2504_;
}
else
{
uint8_t v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = 0;
v___x_2506_ = lean_box(v___x_2505_);
v___x_2507_ = lean_apply_2(v_toPure_2500_, lean_box(0), v___x_2506_);
return v___x_2507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__0___boxed(lean_object* v_toPure_2508_, lean_object* v_b_2509_){
_start:
{
uint8_t v_b_boxed_2510_; lean_object* v_res_2511_; 
v_b_boxed_2510_ = lean_unbox(v_b_2509_);
v_res_2511_ = l_Lean_PersistentArray_allM___redArg___lam__0(v_toPure_2508_, v_b_boxed_2510_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg___lam__1(lean_object* v_p_2512_, lean_object* v_toBind_2513_, lean_object* v___f_2514_, lean_object* v_v_2515_){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_apply_1(v_p_2512_, v_v_2515_);
v___x_2517_ = lean_apply_4(v_toBind_2513_, lean_box(0), lean_box(0), v___x_2516_, v___f_2514_);
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM___redArg(lean_object* v_inst_2518_, lean_object* v_a_2519_, lean_object* v_p_2520_){
_start:
{
lean_object* v_toApplicative_2521_; lean_object* v_toBind_2522_; lean_object* v_toPure_2523_; lean_object* v___f_2524_; lean_object* v___f_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v_toApplicative_2521_ = lean_ctor_get(v_inst_2518_, 0);
v_toBind_2522_ = lean_ctor_get(v_inst_2518_, 1);
lean_inc_n(v_toBind_2522_, 2);
v_toPure_2523_ = lean_ctor_get(v_toApplicative_2521_, 1);
lean_inc(v_toPure_2523_);
v___f_2524_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2524_, 0, v_toPure_2523_);
lean_inc_ref(v___f_2524_);
v___f_2525_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2525_, 0, v_p_2520_);
lean_closure_set(v___f_2525_, 1, v_toBind_2522_);
lean_closure_set(v___f_2525_, 2, v___f_2524_);
v___x_2526_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2518_, v_a_2519_, v___f_2525_);
v___x_2527_ = lean_apply_4(v_toBind_2522_, lean_box(0), lean_box(0), v___x_2526_, v___f_2524_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_allM(lean_object* v_00_u03b1_2528_, lean_object* v_m_2529_, lean_object* v_inst_2530_, lean_object* v_a_2531_, lean_object* v_p_2532_){
_start:
{
lean_object* v_toApplicative_2533_; lean_object* v_toBind_2534_; lean_object* v_toPure_2535_; lean_object* v___f_2536_; lean_object* v___f_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_toApplicative_2533_ = lean_ctor_get(v_inst_2530_, 0);
v_toBind_2534_ = lean_ctor_get(v_inst_2530_, 1);
lean_inc_n(v_toBind_2534_, 2);
v_toPure_2535_ = lean_ctor_get(v_toApplicative_2533_, 1);
lean_inc(v_toPure_2535_);
v___f_2536_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2536_, 0, v_toPure_2535_);
lean_inc_ref(v___f_2536_);
v___f_2537_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_allM___redArg___lam__1), 4, 3);
lean_closure_set(v___f_2537_, 0, v_p_2532_);
lean_closure_set(v___f_2537_, 1, v_toBind_2534_);
lean_closure_set(v___f_2537_, 2, v___f_2536_);
v___x_2538_ = l_Lean_PersistentArray_anyM___redArg(v_inst_2530_, v_a_2531_, v___f_2537_);
v___x_2539_ = lean_apply_4(v_toBind_2534_, lean_box(0), lean_box(0), v___x_2538_, v___f_2536_);
return v___x_2539_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg___lam__0(lean_object* v_p_2540_, lean_object* v_x_2541_){
_start:
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = lean_apply_1(v_p_2540_, v_x_2541_);
v___x_2543_ = lean_unbox(v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___lam__0___boxed(lean_object* v_p_2544_, lean_object* v_x_2545_){
_start:
{
uint8_t v_res_2546_; lean_object* v_r_2547_; 
v_res_2546_ = l_Lean_PersistentArray_any___redArg___lam__0(v_p_2544_, v_x_2545_);
v_r_2547_ = lean_box(v_res_2546_);
return v_r_2547_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any___redArg(lean_object* v_a_2548_, lean_object* v_p_2549_){
_start:
{
lean_object* v___f_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___f_2550_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2550_, 0, v_p_2549_);
v___x_2551_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2552_ = l_Lean_PersistentArray_anyM___redArg(v___x_2551_, v_a_2548_, v___f_2550_);
v___x_2553_ = lean_unbox(v___x_2552_);
lean_dec(v___x_2552_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___redArg___boxed(lean_object* v_a_2554_, lean_object* v_p_2555_){
_start:
{
uint8_t v_res_2556_; lean_object* v_r_2557_; 
v_res_2556_ = l_Lean_PersistentArray_any___redArg(v_a_2554_, v_p_2555_);
v_r_2557_ = lean_box(v_res_2556_);
return v_r_2557_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_any(lean_object* v_00_u03b1_2558_, lean_object* v_a_2559_, lean_object* v_p_2560_){
_start:
{
lean_object* v___f_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___f_2561_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_any___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2561_, 0, v_p_2560_);
v___x_2562_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2563_ = l_Lean_PersistentArray_anyM___redArg(v___x_2562_, v_a_2559_, v___f_2561_);
v___x_2564_ = lean_unbox(v___x_2563_);
lean_dec(v___x_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_any___boxed(lean_object* v_00_u03b1_2565_, lean_object* v_a_2566_, lean_object* v_p_2567_){
_start:
{
uint8_t v_res_2568_; lean_object* v_r_2569_; 
v_res_2568_ = l_Lean_PersistentArray_any(v_00_u03b1_2565_, v_a_2566_, v_p_2567_);
v_r_2569_ = lean_box(v_res_2568_);
return v_r_2569_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg___lam__0(lean_object* v_p_2570_, lean_object* v_x_2571_){
_start:
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = lean_apply_1(v_p_2570_, v_x_2571_);
v___x_2573_ = lean_unbox(v___x_2572_);
if (v___x_2573_ == 0)
{
uint8_t v___x_2574_; 
v___x_2574_ = 1;
return v___x_2574_;
}
else
{
uint8_t v___x_2575_; 
v___x_2575_ = 0;
return v___x_2575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___lam__0___boxed(lean_object* v_p_2576_, lean_object* v_x_2577_){
_start:
{
uint8_t v_res_2578_; lean_object* v_r_2579_; 
v_res_2578_ = l_Lean_PersistentArray_all___redArg___lam__0(v_p_2576_, v_x_2577_);
v_r_2579_ = lean_box(v_res_2578_);
return v_r_2579_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all___redArg(lean_object* v_a_2580_, lean_object* v_p_2581_){
_start:
{
lean_object* v___f_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; uint8_t v___x_2585_; 
v___f_2582_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2582_, 0, v_p_2581_);
v___x_2583_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2584_ = l_Lean_PersistentArray_anyM___redArg(v___x_2583_, v_a_2580_, v___f_2582_);
v___x_2585_ = lean_unbox(v___x_2584_);
lean_dec(v___x_2584_);
if (v___x_2585_ == 0)
{
uint8_t v___x_2586_; 
v___x_2586_ = 1;
return v___x_2586_;
}
else
{
uint8_t v___x_2587_; 
v___x_2587_ = 0;
return v___x_2587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___redArg___boxed(lean_object* v_a_2588_, lean_object* v_p_2589_){
_start:
{
uint8_t v_res_2590_; lean_object* v_r_2591_; 
v_res_2590_ = l_Lean_PersistentArray_all___redArg(v_a_2588_, v_p_2589_);
v_r_2591_ = lean_box(v_res_2590_);
return v_r_2591_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_all(lean_object* v_00_u03b1_2592_, lean_object* v_a_2593_, lean_object* v_p_2594_){
_start:
{
lean_object* v___f_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; 
v___f_2595_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_all___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2595_, 0, v_p_2594_);
v___x_2596_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2597_ = l_Lean_PersistentArray_anyM___redArg(v___x_2596_, v_a_2593_, v___f_2595_);
v___x_2598_ = lean_unbox(v___x_2597_);
lean_dec(v___x_2597_);
if (v___x_2598_ == 0)
{
uint8_t v___x_2599_; 
v___x_2599_ = 1;
return v___x_2599_;
}
else
{
uint8_t v___x_2600_; 
v___x_2600_ = 0;
return v___x_2600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_all___boxed(lean_object* v_00_u03b1_2601_, lean_object* v_a_2602_, lean_object* v_p_2603_){
_start:
{
uint8_t v_res_2604_; lean_object* v_r_2605_; 
v_res_2604_ = l_Lean_PersistentArray_all(v_00_u03b1_2601_, v_a_2602_, v_p_2603_);
v_r_2605_ = lean_box(v_res_2604_);
return v_r_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__0(lean_object* v_cs_2606_){
_start:
{
lean_object* v___x_2607_; 
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v_cs_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__2(lean_object* v_vs_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2609_, 0, v_vs_2608_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg(lean_object* v_inst_2612_, lean_object* v_f_2613_, lean_object* v_x_2614_){
_start:
{
if (lean_obj_tag(v_x_2614_) == 0)
{
lean_object* v_toApplicative_2615_; lean_object* v_toFunctor_2616_; lean_object* v_cs_2617_; lean_object* v_map_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; size_t v_sz_2621_; size_t v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v_toApplicative_2615_ = lean_ctor_get(v_inst_2612_, 0);
v_toFunctor_2616_ = lean_ctor_get(v_toApplicative_2615_, 0);
v_cs_2617_ = lean_ctor_get(v_x_2614_, 0);
lean_inc_ref(v_cs_2617_);
lean_dec_ref_known(v_x_2614_, 1);
v_map_2618_ = lean_ctor_get(v_toFunctor_2616_, 0);
lean_inc(v_map_2618_);
v___f_2619_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__0));
lean_inc_ref(v_inst_2612_);
v___f_2620_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapMAux___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2620_, 0, v_inst_2612_);
lean_closure_set(v___f_2620_, 1, v_f_2613_);
v_sz_2621_ = lean_array_size(v_cs_2617_);
v___x_2622_ = ((size_t)0ULL);
v___x_2623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2612_, v___f_2620_, v_sz_2621_, v___x_2622_, v_cs_2617_);
v___x_2624_ = lean_apply_4(v_map_2618_, lean_box(0), lean_box(0), v___f_2619_, v___x_2623_);
return v___x_2624_;
}
else
{
lean_object* v_toApplicative_2625_; lean_object* v_toFunctor_2626_; lean_object* v_vs_2627_; lean_object* v_map_2628_; lean_object* v___f_2629_; size_t v_sz_2630_; size_t v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v_toApplicative_2625_ = lean_ctor_get(v_inst_2612_, 0);
v_toFunctor_2626_ = lean_ctor_get(v_toApplicative_2625_, 0);
v_vs_2627_ = lean_ctor_get(v_x_2614_, 0);
lean_inc_ref(v_vs_2627_);
lean_dec_ref_known(v_x_2614_, 1);
v_map_2628_ = lean_ctor_get(v_toFunctor_2626_, 0);
lean_inc(v_map_2628_);
v___f_2629_ = ((lean_object*)(l_Lean_PersistentArray_mapMAux___redArg___closed__1));
v_sz_2630_ = lean_array_size(v_vs_2627_);
v___x_2631_ = ((size_t)0ULL);
v___x_2632_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2612_, v_f_2613_, v_sz_2630_, v___x_2631_, v_vs_2627_);
v___x_2633_ = lean_apply_4(v_map_2628_, lean_box(0), lean_box(0), v___f_2629_, v___x_2632_);
return v___x_2633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux___redArg___lam__1(lean_object* v_inst_2634_, lean_object* v_f_2635_, lean_object* v_c_2636_){
_start:
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2634_, v_f_2635_, v_c_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapMAux(lean_object* v_00_u03b1_2638_, lean_object* v_m_2639_, lean_object* v_inst_2640_, lean_object* v_00_u03b2_2641_, lean_object* v_f_2642_, lean_object* v_x_2643_){
_start:
{
lean_object* v___x_2644_; 
v___x_2644_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2640_, v_f_2642_, v_x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0(lean_object* v_root_2645_, lean_object* v_size_2646_, size_t v_shift_2647_, lean_object* v_tailOff_2648_, lean_object* v_toPure_2649_, lean_object* v_tail_2650_){
_start:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2651_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2651_, 0, v_root_2645_);
lean_ctor_set(v___x_2651_, 1, v_tail_2650_);
lean_ctor_set(v___x_2651_, 2, v_size_2646_);
lean_ctor_set(v___x_2651_, 3, v_tailOff_2648_);
lean_ctor_set_usize(v___x_2651_, 4, v_shift_2647_);
v___x_2652_ = lean_apply_2(v_toPure_2649_, lean_box(0), v___x_2651_);
return v___x_2652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__0___boxed(lean_object* v_root_2653_, lean_object* v_size_2654_, lean_object* v_shift_2655_, lean_object* v_tailOff_2656_, lean_object* v_toPure_2657_, lean_object* v_tail_2658_){
_start:
{
size_t v_shift_boxed_2659_; lean_object* v_res_2660_; 
v_shift_boxed_2659_ = lean_unbox_usize(v_shift_2655_);
lean_dec(v_shift_2655_);
v_res_2660_ = l_Lean_PersistentArray_mapM___redArg___lam__0(v_root_2653_, v_size_2654_, v_shift_boxed_2659_, v_tailOff_2656_, v_toPure_2657_, v_tail_2658_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1(lean_object* v_size_2661_, size_t v_shift_2662_, lean_object* v_tailOff_2663_, lean_object* v_toPure_2664_, lean_object* v_tail_2665_, lean_object* v_inst_2666_, lean_object* v_f_2667_, lean_object* v_toBind_2668_, lean_object* v_root_2669_){
_start:
{
lean_object* v___x_2670_; lean_object* v___f_2671_; size_t v_sz_2672_; size_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2670_ = lean_box_usize(v_shift_2662_);
v___f_2671_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2671_, 0, v_root_2669_);
lean_closure_set(v___f_2671_, 1, v_size_2661_);
lean_closure_set(v___f_2671_, 2, v___x_2670_);
lean_closure_set(v___f_2671_, 3, v_tailOff_2663_);
lean_closure_set(v___f_2671_, 4, v_toPure_2664_);
v_sz_2672_ = lean_array_size(v_tail_2665_);
v___x_2673_ = ((size_t)0ULL);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_2666_, v_f_2667_, v_sz_2672_, v___x_2673_, v_tail_2665_);
v___x_2675_ = lean_apply_4(v_toBind_2668_, lean_box(0), lean_box(0), v___x_2674_, v___f_2671_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg___lam__1___boxed(lean_object* v_size_2676_, lean_object* v_shift_2677_, lean_object* v_tailOff_2678_, lean_object* v_toPure_2679_, lean_object* v_tail_2680_, lean_object* v_inst_2681_, lean_object* v_f_2682_, lean_object* v_toBind_2683_, lean_object* v_root_2684_){
_start:
{
size_t v_shift_boxed_2685_; lean_object* v_res_2686_; 
v_shift_boxed_2685_ = lean_unbox_usize(v_shift_2677_);
lean_dec(v_shift_2677_);
v_res_2686_ = l_Lean_PersistentArray_mapM___redArg___lam__1(v_size_2676_, v_shift_boxed_2685_, v_tailOff_2678_, v_toPure_2679_, v_tail_2680_, v_inst_2681_, v_f_2682_, v_toBind_2683_, v_root_2684_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM___redArg(lean_object* v_inst_2687_, lean_object* v_f_2688_, lean_object* v_t_2689_){
_start:
{
lean_object* v_toApplicative_2690_; lean_object* v_toBind_2691_; lean_object* v_root_2692_; lean_object* v_tail_2693_; lean_object* v_size_2694_; size_t v_shift_2695_; lean_object* v_tailOff_2696_; lean_object* v_toPure_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___f_2700_; lean_object* v___x_2701_; 
v_toApplicative_2690_ = lean_ctor_get(v_inst_2687_, 0);
v_toBind_2691_ = lean_ctor_get(v_inst_2687_, 1);
lean_inc_n(v_toBind_2691_, 2);
v_root_2692_ = lean_ctor_get(v_t_2689_, 0);
lean_inc_ref(v_root_2692_);
v_tail_2693_ = lean_ctor_get(v_t_2689_, 1);
lean_inc_ref(v_tail_2693_);
v_size_2694_ = lean_ctor_get(v_t_2689_, 2);
lean_inc(v_size_2694_);
v_shift_2695_ = lean_ctor_get_usize(v_t_2689_, 4);
v_tailOff_2696_ = lean_ctor_get(v_t_2689_, 3);
lean_inc(v_tailOff_2696_);
lean_dec_ref(v_t_2689_);
v_toPure_2697_ = lean_ctor_get(v_toApplicative_2690_, 1);
lean_inc(v_toPure_2697_);
lean_inc(v_f_2688_);
lean_inc_ref(v_inst_2687_);
v___x_2698_ = l_Lean_PersistentArray_mapMAux___redArg(v_inst_2687_, v_f_2688_, v_root_2692_);
v___x_2699_ = lean_box_usize(v_shift_2695_);
v___f_2700_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_mapM___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2700_, 0, v_size_2694_);
lean_closure_set(v___f_2700_, 1, v___x_2699_);
lean_closure_set(v___f_2700_, 2, v_tailOff_2696_);
lean_closure_set(v___f_2700_, 3, v_toPure_2697_);
lean_closure_set(v___f_2700_, 4, v_tail_2693_);
lean_closure_set(v___f_2700_, 5, v_inst_2687_);
lean_closure_set(v___f_2700_, 6, v_f_2688_);
lean_closure_set(v___f_2700_, 7, v_toBind_2691_);
v___x_2701_ = lean_apply_4(v_toBind_2691_, lean_box(0), lean_box(0), v___x_2698_, v___f_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_mapM(lean_object* v_00_u03b1_2702_, lean_object* v_m_2703_, lean_object* v_inst_2704_, lean_object* v_00_u03b2_2705_, lean_object* v_f_2706_, lean_object* v_t_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_PersistentArray_mapM___redArg(v_inst_2704_, v_f_2706_, v_t_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg___lam__0(lean_object* v_f_2709_, lean_object* v_x_2710_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = lean_apply_1(v_f_2709_, v_x_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map___redArg(lean_object* v_f_2712_, lean_object* v_t_2713_){
_start:
{
lean_object* v___f_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v___f_2714_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2714_, 0, v_f_2712_);
v___x_2715_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2716_ = l_Lean_PersistentArray_mapM___redArg(v___x_2715_, v___f_2714_, v_t_2713_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_map(lean_object* v_00_u03b1_2717_, lean_object* v_00_u03b2_2718_, lean_object* v_f_2719_, lean_object* v_t_2720_){
_start:
{
lean_object* v___f_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___f_2721_ = lean_alloc_closure((void*)(l_Lean_PersistentArray_map___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2721_, 0, v_f_2719_);
v___x_2722_ = ((lean_object*)(l_Lean_PersistentArray_foldl___redArg___closed__9));
v___x_2723_ = l_Lean_PersistentArray_mapM___redArg(v___x_2722_, v___f_2721_, v_t_2720_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg(lean_object* v_x_2724_, lean_object* v_x_2725_, lean_object* v_x_2726_){
_start:
{
if (lean_obj_tag(v_x_2724_) == 0)
{
lean_object* v_cs_2727_; lean_object* v_numNodes_2728_; lean_object* v_depth_2729_; lean_object* v_tailSize_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2752_; 
v_cs_2727_ = lean_ctor_get(v_x_2724_, 0);
v_numNodes_2728_ = lean_ctor_get(v_x_2725_, 0);
v_depth_2729_ = lean_ctor_get(v_x_2725_, 1);
v_tailSize_2730_ = lean_ctor_get(v_x_2725_, 2);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_x_2725_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2732_ = v_x_2725_;
v_isShared_2733_ = v_isSharedCheck_2752_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_tailSize_2730_);
lean_inc(v_depth_2729_);
lean_inc(v_numNodes_2728_);
lean_dec(v_x_2725_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2752_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___y_2737_; uint8_t v___x_2751_; 
v___x_2734_ = lean_unsigned_to_nat(1u);
v___x_2735_ = lean_nat_add(v_numNodes_2728_, v___x_2734_);
lean_dec(v_numNodes_2728_);
v___x_2751_ = lean_nat_dec_le(v_x_2726_, v_depth_2729_);
if (v___x_2751_ == 0)
{
lean_dec(v_depth_2729_);
lean_inc(v_x_2726_);
v___y_2737_ = v_x_2726_;
goto v___jp_2736_;
}
else
{
v___y_2737_ = v_depth_2729_;
goto v___jp_2736_;
}
v___jp_2736_:
{
lean_object* v___x_2739_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 1, v___y_2737_);
lean_ctor_set(v___x_2732_, 0, v___x_2735_);
v___x_2739_ = v___x_2732_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v___y_2737_);
lean_ctor_set(v_reuseFailAlloc_2750_, 2, v_tailSize_2730_);
v___x_2739_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v___x_2740_ = lean_unsigned_to_nat(0u);
v___x_2741_ = lean_array_get_size(v_cs_2727_);
v___x_2742_ = lean_nat_dec_lt(v___x_2740_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_dec(v_x_2726_);
return v___x_2739_;
}
else
{
uint8_t v___x_2743_; 
v___x_2743_ = lean_nat_dec_le(v___x_2741_, v___x_2741_);
if (v___x_2743_ == 0)
{
if (v___x_2742_ == 0)
{
lean_dec(v_x_2726_);
return v___x_2739_;
}
else
{
size_t v___x_2744_; size_t v___x_2745_; lean_object* v___x_2746_; 
v___x_2744_ = ((size_t)0ULL);
v___x_2745_ = lean_usize_of_nat(v___x_2741_);
v___x_2746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2726_, v_cs_2727_, v___x_2744_, v___x_2745_, v___x_2739_);
lean_dec(v_x_2726_);
return v___x_2746_;
}
}
else
{
size_t v___x_2747_; size_t v___x_2748_; lean_object* v___x_2749_; 
v___x_2747_ = ((size_t)0ULL);
v___x_2748_ = lean_usize_of_nat(v___x_2741_);
v___x_2749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2726_, v_cs_2727_, v___x_2747_, v___x_2748_, v___x_2739_);
lean_dec(v_x_2726_);
return v___x_2749_;
}
}
}
}
}
}
else
{
lean_object* v_numNodes_2753_; lean_object* v_depth_2754_; lean_object* v_tailSize_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2768_; 
v_numNodes_2753_ = lean_ctor_get(v_x_2725_, 0);
v_depth_2754_ = lean_ctor_get(v_x_2725_, 1);
v_tailSize_2755_ = lean_ctor_get(v_x_2725_, 2);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_x_2725_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2757_ = v_x_2725_;
v_isShared_2758_ = v_isSharedCheck_2768_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_tailSize_2755_);
lean_inc(v_depth_2754_);
lean_inc(v_numNodes_2753_);
lean_dec(v_x_2725_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2768_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v___x_2759_ = lean_unsigned_to_nat(1u);
v___x_2760_ = lean_nat_add(v_numNodes_2753_, v___x_2759_);
lean_dec(v_numNodes_2753_);
v___x_2761_ = lean_nat_dec_le(v_x_2726_, v_depth_2754_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2763_; 
lean_dec(v_depth_2754_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v_x_2726_);
lean_ctor_set(v___x_2757_, 0, v___x_2760_);
v___x_2763_ = v___x_2757_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v_x_2726_);
lean_ctor_set(v_reuseFailAlloc_2764_, 2, v_tailSize_2755_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
else
{
lean_object* v___x_2766_; 
lean_dec(v_x_2726_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2760_);
v___x_2766_ = v___x_2757_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_depth_2754_);
lean_ctor_set(v_reuseFailAlloc_2767_, 2, v_tailSize_2755_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(lean_object* v_x_2769_, lean_object* v_as_2770_, size_t v_i_2771_, size_t v_stop_2772_, lean_object* v_b_2773_){
_start:
{
uint8_t v___x_2774_; 
v___x_2774_ = lean_usize_dec_eq(v_i_2771_, v_stop_2772_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; size_t v___x_2779_; size_t v___x_2780_; 
v___x_2775_ = lean_array_uget_borrowed(v_as_2770_, v_i_2771_);
v___x_2776_ = lean_unsigned_to_nat(1u);
v___x_2777_ = lean_nat_add(v_x_2769_, v___x_2776_);
v___x_2778_ = l_Lean_PersistentArray_collectStats___redArg(v___x_2775_, v_b_2773_, v___x_2777_);
v___x_2779_ = ((size_t)1ULL);
v___x_2780_ = lean_usize_add(v_i_2771_, v___x_2779_);
v_i_2771_ = v___x_2780_;
v_b_2773_ = v___x_2778_;
goto _start;
}
else
{
return v_b_2773_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg___boxed(lean_object* v_x_2782_, lean_object* v_as_2783_, lean_object* v_i_2784_, lean_object* v_stop_2785_, lean_object* v_b_2786_){
_start:
{
size_t v_i_boxed_2787_; size_t v_stop_boxed_2788_; lean_object* v_res_2789_; 
v_i_boxed_2787_ = lean_unbox_usize(v_i_2784_);
lean_dec(v_i_2784_);
v_stop_boxed_2788_ = lean_unbox_usize(v_stop_2785_);
lean_dec(v_stop_2785_);
v_res_2789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2782_, v_as_2783_, v_i_boxed_2787_, v_stop_boxed_2788_, v_b_2786_);
lean_dec_ref(v_as_2783_);
lean_dec(v_x_2782_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___redArg___boxed(lean_object* v_x_2790_, lean_object* v_x_2791_, lean_object* v_x_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2790_, v_x_2791_, v_x_2792_);
lean_dec_ref(v_x_2790_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats(lean_object* v_00_u03b1_2794_, lean_object* v_x_2795_, lean_object* v_x_2796_, lean_object* v_x_2797_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_PersistentArray_collectStats___redArg(v_x_2795_, v_x_2796_, v_x_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_collectStats___boxed(lean_object* v_00_u03b1_2799_, lean_object* v_x_2800_, lean_object* v_x_2801_, lean_object* v_x_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Lean_PersistentArray_collectStats(v_00_u03b1_2799_, v_x_2800_, v_x_2801_, v_x_2802_);
lean_dec_ref(v_x_2800_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(lean_object* v_00_u03b1_2804_, lean_object* v_x_2805_, lean_object* v_as_2806_, size_t v_i_2807_, size_t v_stop_2808_, lean_object* v_b_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___redArg(v_x_2805_, v_as_2806_, v_i_2807_, v_stop_2808_, v_b_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0___boxed(lean_object* v_00_u03b1_2811_, lean_object* v_x_2812_, lean_object* v_as_2813_, lean_object* v_i_2814_, lean_object* v_stop_2815_, lean_object* v_b_2816_){
_start:
{
size_t v_i_boxed_2817_; size_t v_stop_boxed_2818_; lean_object* v_res_2819_; 
v_i_boxed_2817_ = lean_unbox_usize(v_i_2814_);
lean_dec(v_i_2814_);
v_stop_boxed_2818_ = lean_unbox_usize(v_stop_2815_);
lean_dec(v_stop_2815_);
v_res_2819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_collectStats_spec__0(v_00_u03b1_2811_, v_x_2812_, v_as_2813_, v_i_boxed_2817_, v_stop_boxed_2818_, v_b_2816_);
lean_dec_ref(v_as_2813_);
lean_dec(v_x_2812_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg(lean_object* v_r_2820_){
_start:
{
lean_object* v_root_2821_; lean_object* v_tail_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_root_2821_ = lean_ctor_get(v_r_2820_, 0);
v_tail_2822_ = lean_ctor_get(v_r_2820_, 1);
v___x_2823_ = lean_unsigned_to_nat(0u);
v___x_2824_ = lean_array_get_size(v_tail_2822_);
v___x_2825_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2823_);
lean_ctor_set(v___x_2825_, 1, v___x_2823_);
lean_ctor_set(v___x_2825_, 2, v___x_2824_);
v___x_2826_ = l_Lean_PersistentArray_collectStats___redArg(v_root_2821_, v___x_2825_, v___x_2823_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___redArg___boxed(lean_object* v_r_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_PersistentArray_stats___redArg(v_r_2827_);
lean_dec_ref(v_r_2827_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats(lean_object* v_00_u03b1_2829_, lean_object* v_r_2830_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l_Lean_PersistentArray_stats___redArg(v_r_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_stats___boxed(lean_object* v_00_u03b1_2832_, lean_object* v_r_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_PersistentArray_stats(v_00_u03b1_2832_, v_r_2833_);
lean_dec_ref(v_r_2833_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_Stats_toString(lean_object* v_s_2839_){
_start:
{
lean_object* v_numNodes_2840_; lean_object* v_depth_2841_; lean_object* v_tailSize_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; 
v_numNodes_2840_ = lean_ctor_get(v_s_2839_, 0);
lean_inc(v_numNodes_2840_);
v_depth_2841_ = lean_ctor_get(v_s_2839_, 1);
lean_inc(v_depth_2841_);
v_tailSize_2842_ = lean_ctor_get(v_s_2839_, 2);
lean_inc(v_tailSize_2842_);
lean_dec_ref(v_s_2839_);
v___x_2843_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__0));
v___x_2844_ = l_Nat_reprFast(v_numNodes_2840_);
v___x_2845_ = lean_string_append(v___x_2843_, v___x_2844_);
lean_dec_ref(v___x_2844_);
v___x_2846_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__1));
v___x_2847_ = lean_string_append(v___x_2845_, v___x_2846_);
v___x_2848_ = l_Nat_reprFast(v_depth_2841_);
v___x_2849_ = lean_string_append(v___x_2847_, v___x_2848_);
lean_dec_ref(v___x_2848_);
v___x_2850_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__2));
v___x_2851_ = lean_string_append(v___x_2849_, v___x_2850_);
v___x_2852_ = l_Nat_reprFast(v_tailSize_2842_);
v___x_2853_ = lean_string_append(v___x_2851_, v___x_2852_);
lean_dec_ref(v___x_2852_);
v___x_2854_ = ((lean_object*)(l_Lean_PersistentArray_Stats_toString___closed__3));
v___x_2855_ = lean_string_append(v___x_2853_, v___x_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(lean_object* v_v_2858_, lean_object* v_j_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_zero_2861_; uint8_t v_isZero_2862_; 
v_zero_2861_ = lean_unsigned_to_nat(0u);
v_isZero_2862_ = lean_nat_dec_eq(v_j_2859_, v_zero_2861_);
if (v_isZero_2862_ == 1)
{
lean_dec(v_j_2859_);
lean_dec(v_v_2858_);
return v_a_2860_;
}
else
{
lean_object* v_one_2863_; lean_object* v_n_2864_; lean_object* v___x_2865_; 
v_one_2863_ = lean_unsigned_to_nat(1u);
v_n_2864_ = lean_nat_sub(v_j_2859_, v_one_2863_);
lean_dec(v_j_2859_);
lean_inc(v_v_2858_);
v___x_2865_ = l_Lean_PersistentArray_push___redArg(v_a_2860_, v_v_2858_);
v_j_2859_ = v_n_2864_;
v_a_2860_ = v___x_2865_;
goto _start;
}
}
}
static lean_object* _init_l_Lean_mkPersistentArray___redArg___closed__0(void){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_PersistentArray_empty(lean_box(0));
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray___redArg(lean_object* v_n_2868_, lean_object* v_v_2869_){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_obj_once(&l_Lean_mkPersistentArray___redArg___closed__0, &l_Lean_mkPersistentArray___redArg___closed__0_once, _init_l_Lean_mkPersistentArray___redArg___closed__0);
v___x_2871_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2869_, v_n_2868_, v___x_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPersistentArray(lean_object* v_00_u03b1_2872_, lean_object* v_n_2873_, lean_object* v_v_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_mkPersistentArray___redArg(v_n_2873_, v_v_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(lean_object* v_00_u03b1_2876_, lean_object* v_v_2877_, lean_object* v_n_2878_, lean_object* v_j_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v___x_2882_; 
v___x_2882_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___redArg(v_v_2877_, v_j_2879_, v_a_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0___boxed(lean_object* v_00_u03b1_2883_, lean_object* v_v_2884_, lean_object* v_n_2885_, lean_object* v_j_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop___at___00Lean_mkPersistentArray_spec__0(v_00_u03b1_2883_, v_v_2884_, v_n_2885_, v_j_2886_, v_a_2887_, v_a_2888_);
lean_dec(v_n_2885_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray___redArg(lean_object* v_n_2890_, lean_object* v_v_2891_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lean_mkPersistentArray___redArg(v_n_2890_, v_v_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPArray(lean_object* v_00_u03b1_2893_, lean_object* v_n_2894_, lean_object* v_v_2895_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Lean_mkPersistentArray___redArg(v_n_2894_, v_v_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
if (lean_obj_tag(v_a_2897_) == 0)
{
return v_a_2898_;
}
else
{
lean_object* v_head_2899_; lean_object* v_tail_2900_; lean_object* v___x_2901_; 
v_head_2899_ = lean_ctor_get(v_a_2897_, 0);
lean_inc(v_head_2899_);
v_tail_2900_ = lean_ctor_get(v_a_2897_, 1);
lean_inc(v_tail_2900_);
lean_dec_ref_known(v_a_2897_, 2);
v___x_2901_ = l_Lean_PersistentArray_push___redArg(v_a_2898_, v_head_2899_);
v_a_2897_ = v_tail_2900_;
v_a_2898_ = v___x_2901_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop(lean_object* v_00_u03b1_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_a_2904_, v_a_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27___redArg(lean_object* v_xs_2907_){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2908_ = lean_unsigned_to_nat(32u);
v___x_2909_ = lean_mk_empty_array_with_capacity(v___x_2908_);
lean_dec_ref(v___x_2909_);
v___x_2910_ = lean_obj_once(&l_Lean_instInhabitedPersistentArray_default___closed__1, &l_Lean_instInhabitedPersistentArray_default___closed__1_once, _init_l_Lean_instInhabitedPersistentArray_default___closed__1);
v___x_2911_ = l___private_Lean_Data_PersistentArray_0__Lean_List_toPArray_x27_loop___redArg(v_xs_2907_, v___x_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toPArray_x27(lean_object* v_00_u03b1_2912_, lean_object* v_xs_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Lean_List_toPArray_x27___redArg(v_xs_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg(lean_object* v_xs_2915_){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2916_ = lean_obj_once(&l_Lean_mkPersistentArray___redArg___closed__0, &l_Lean_mkPersistentArray___redArg___closed__0_once, _init_l_Lean_mkPersistentArray___redArg___closed__0);
v___x_2917_ = lean_unsigned_to_nat(0u);
v___x_2918_ = lean_array_get_size(v_xs_2915_);
v___x_2919_ = lean_nat_dec_lt(v___x_2917_, v___x_2918_);
if (v___x_2919_ == 0)
{
return v___x_2916_;
}
else
{
uint8_t v___x_2920_; 
v___x_2920_ = lean_nat_dec_le(v___x_2918_, v___x_2918_);
if (v___x_2920_ == 0)
{
if (v___x_2919_ == 0)
{
return v___x_2916_;
}
else
{
size_t v___x_2921_; size_t v___x_2922_; lean_object* v___x_2923_; 
v___x_2921_ = ((size_t)0ULL);
v___x_2922_ = lean_usize_of_nat(v___x_2918_);
v___x_2923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_2915_, v___x_2921_, v___x_2922_, v___x_2916_);
return v___x_2923_;
}
}
else
{
size_t v___x_2924_; size_t v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = ((size_t)0ULL);
v___x_2925_ = lean_usize_of_nat(v___x_2918_);
v___x_2926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_PersistentArray_append_spec__0_spec__1___redArg(v_xs_2915_, v___x_2924_, v___x_2925_, v___x_2916_);
return v___x_2926_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___redArg___boxed(lean_object* v_xs_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Array_toPArray_x27___redArg(v_xs_2927_);
lean_dec_ref(v_xs_2927_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27(lean_object* v_00_u03b1_2929_, lean_object* v_xs_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_Array_toPArray_x27___redArg(v_xs_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toPArray_x27___boxed(lean_object* v_00_u03b1_2932_, lean_object* v_xs_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_Array_toPArray_x27(v_00_u03b1_2932_, v_xs_2933_);
lean_dec_ref(v_xs_2933_);
return v_res_2934_;
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
